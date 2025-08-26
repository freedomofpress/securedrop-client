#!/usr/bin/env python3
import os
from unittest.mock import patch

import pytest
from configure_onion_service import (
    ARTI_KEY_FILENAME,
    convert_onion_client_key,
    get_env,
    setup_journalist_access,
)

# File stat bit mask, used to obtain file permissions
PERM_BITMASK = 0o777


@pytest.fixture
def qubesdb_mock(mocker):
    qubesdb_mock = mocker.MagicMock()
    qubesdb_mock.read.side_effect = "42"
    mocker.patch("configure_onion_service.QubesDB", side_effect=qubesdb_mock)
    return qubesdb_mock.return_value


@pytest.mark.parametrize(
    ("keys", "expected_env"),
    [(["key"], {"key": "value"}), (["key1", "key2"], {"key1": "value1", "key2": "value2"})],
)
def test_get_env(keys, expected_env, qubesdb_mock):
    qubesdb_mock.read.side_effect = [v.encode() for v in expected_env.values()]
    assert expected_env == get_env(keys)


@pytest.mark.parametrize(
    ("ctor_key", "arti_key"),
    [
        (
            "DKBZHBQUBTVSHCO62IEBOUTXFUA7TVTFBSH2Y7CQREMVWUZ72ZKQ",
            """-----BEGIN OPENSSH PRIVATE KEY-----
b3BlbnNzaC1rZXktdjEAAAAABG5vbmUAAAAEbm9uZQAAAAAAAAABAAAAQgAAABp4MjU1MT
lAc3BlYy50b3Jwcm9qZWN0Lm9yZwAAACCH0gGiwMNLM9nXuS5Y3jjyC3jQKYufpk2ij4Uc
AUnnfAAAAHgAAQIDAAECAwAAABp4MjU1MTlAc3BlYy50b3Jwcm9qZWN0Lm9yZwAAACCH0g
GiwMNLM9nXuS5Y3jjyC3jQKYufpk2ij4UcAUnnfAAAACAYg5OGFAzrI4ne0ggXUnctAfnW
ZQyPrHxQiRlbUz/WVQAAAAABAgMEBQY=
-----END OPENSSH PRIVATE KEY-----""",
        ),
        (
            "4CLLIHTNS7KMOYQIE6XKZ2TDI2S7CYAQAHMFJRQPMHPPEUGX5FEQ",
            """-----BEGIN OPENSSH PRIVATE KEY-----
b3BlbnNzaC1rZXktdjEAAAAABG5vbmUAAAAEbm9uZQAAAAAAAAABAAAAQgAAABp4MjU1MT
lAc3BlYy50b3Jwcm9qZWN0Lm9yZwAAACCt3L/s3fLVYTR61oYR3dpiatITcRaLmKDyqeTO
MclEMwAAAHgAAQIDAAECAwAAABp4MjU1MTlAc3BlYy50b3Jwcm9qZWN0Lm9yZwAAACCt3L
/s3fLVYTR61oYR3dpiatITcRaLmKDyqeTOMclEMwAAACDglrQebZfUx2IIJ66s6mNGpfFg
EAHYVMYPYd7yUNfpSQAAAAABAgMEBQY=
-----END OPENSSH PRIVATE KEY-----""",
        ),
        (
            "TMNSKMJYP7FYYDJNRT5ATGRMWUG34DNQOXVTEVCDVCIIRV66RUCA",
            """-----BEGIN OPENSSH PRIVATE KEY-----
b3BlbnNzaC1rZXktdjEAAAAABG5vbmUAAAAEbm9uZQAAAAAAAAABAAAAQgAAABp4MjU1MT
lAc3BlYy50b3Jwcm9qZWN0Lm9yZwAAACALhKtBxmb9cmMqaaK82zmvbt8xedPeSR8xdDay
5f1NWwAAAHgAAQIDAAECAwAAABp4MjU1MTlAc3BlYy50b3Jwcm9qZWN0Lm9yZwAAACALhK
tBxmb9cmMqaaK82zmvbt8xedPeSR8xdDay5f1NWwAAACCYGyUxOH/LjA0tjPoJmiy1Db4N
sHXrMlRDqJCI196NRAAAAAABAgMEBQY=
-----END OPENSSH PRIVATE KEY-----""",
        ),
    ],
)
@patch(  # Mock os.urandom to return a specific value when called with 4
    "os.urandom", side_effect=lambda n: b"\x00\x01\x02\x03" if n == 4 else os.urandom(n)
)
def test_convert_onion_client_key(urandom_patch, ctor_key, arti_key):
    assert arti_key == convert_onion_client_key(ctor_key)


@patch("configure_onion_service.convert_onion_client_key", return_value="MOCKED_KEY")
def test_setup_journalist_access(mocker, tmp_path):
    hidserv_key = "TMNSKMJYP7FYYDJNRT5ATGRMWUG34DNQOXVTEVCDVCIIRV66RUCA"
    hidserv_id = "SOME_HOSTNAME_WITHOUT_DOT_ONION"
    hidserv_hostname = f"http://{hidserv_id}.onion"
    setup_journalist_access(tmp_path, hidserv_key, hidserv_hostname)

    key_dir = tmp_path / "client" / hidserv_id
    key_path = key_dir / ARTI_KEY_FILENAME
    # Folder isn't world-readable
    assert os.stat(key_dir).st_mode & PERM_BITMASK == 0o700
    # And the umask controlled the parent directory permissions
    assert os.stat(key_dir.parent).st_mode & PERM_BITMASK == 0o700
    # Same with the keyfile
    assert os.stat(key_path).st_mode & PERM_BITMASK == 0o600

    assert key_path.read_text() == "MOCKED_KEY"
