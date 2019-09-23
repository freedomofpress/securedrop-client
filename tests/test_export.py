import os
import pytest
import subprocess
from tempfile import TemporaryDirectory, NamedTemporaryFile

from securedrop_client.export import Export, ExportError


def test_send_file_to_usb_device(mocker):
    '''
    Ensure TemporaryDirectory is used when creating and sending the archive containing the export
    file.
    '''
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value='mock_temp_dir')
    mocker.patch('securedrop_client.export.TemporaryDirectory', return_value=mock_temp_dir)
    export = Export()
    _run_disk_export = mocker.patch.object(export, '_run_disk_export')

    export.send_file_to_usb_device(['mock_filepath'], 'mock passphrase')

    _run_disk_export.assert_called_once_with('mock_temp_dir', ['mock_filepath'], 'mock passphrase')


def test_run_preflight_checks(mocker):
    '''
    Ensure TemporaryDirectory is used when creating and sending the archives during the preflight
    checks.
    '''
    mock_temp_dir = mocker.MagicMock()
    mock_temp_dir.__enter__ = mocker.MagicMock(return_value='mock_temp_dir')
    mocker.patch('securedrop_client.export.TemporaryDirectory', return_value=mock_temp_dir)
    export = Export()
    _run_usb_export = mocker.patch.object(export, '_run_usb_test')
    _run_disk_export = mocker.patch.object(export, '_run_disk_test')

    export.run_preflight_checks()

    _run_usb_export.assert_called_once_with('mock_temp_dir')
    _run_disk_export.assert_called_once_with('mock_temp_dir')


def test__run_disk_export(mocker):
    '''
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if '' is the ouput status of _export_archive.
    '''
    export = Export()
    export._create_archive = mocker.MagicMock(return_value='mock_archive_path')
    export._export_archive = mocker.MagicMock(return_value='')

    export._run_disk_export('mock_archive_dir', ['mock_filepath'], 'mock_passphrase')

    export._export_archive.assert_called_once_with('mock_archive_path')
    export._create_archive.assert_called_once_with(
        'mock_archive_dir',
        'archive.sd-export',
        {
            'encryption_key': 'mock_passphrase',
            'device': 'disk',
            'encryption_method': 'luks'
        },
        ['mock_filepath'])


def test__run_disk_export_raises_ExportError_if_not_empty_string(mocker):
    '''
    Ensure ExportError is raised if _run_disk_test returns anything other than ''.
    '''
    export = Export()
    export._create_archive = mocker.MagicMock(return_value='mock_archive_path')
    export._export_archive = mocker.MagicMock(return_value='SOMETHING_OTHER_THAN_EMPTY_STRING')

    with pytest.raises(ExportError):
        export._run_disk_export('mock_archive_dir', ['mock_filepath'], 'mock_passphrase')


def test__run_disk_test(mocker):
    '''
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if 'USB_ENCRYPTED' is the ouput status of _export_archive.
    '''
    export = Export()
    export._create_archive = mocker.MagicMock(return_value='mock_archive_path')
    export._export_archive = mocker.MagicMock(return_value='USB_ENCRYPTED')

    export._run_disk_test('mock_archive_dir')

    export._export_archive.assert_called_once_with('mock_archive_path')
    export._create_archive.assert_called_once_with(
        'mock_archive_dir', 'disk-test.sd-export', {'device': 'disk-test'})


def test__run_disk_test_raises_ExportError_if_not_USB_ENCRYPTED(mocker):
    '''
    Ensure ExportError is raised if _run_disk_test returns anything other than 'USB_ENCRYPTED'.
    '''
    export = Export()
    export._create_archive = mocker.MagicMock(return_value='mock_archive_path')
    export._export_archive = mocker.MagicMock(return_value='SOMETHING_OTHER_THAN_USB_ENCRYPTED')

    with pytest.raises(ExportError):
        export._run_disk_test('mock_archive_dir')


def test__run_usb_test(mocker):
    '''
    Ensure _export_archive and _create_archive are called with the expected parameters,
    _export_archive is called with the return value of _create_archive, and
    _run_disk_test returns without error if 'USB_CONNECTED' is the return value of _export_archive.
    '''
    export = Export()
    export._create_archive = mocker.MagicMock(return_value='mock_archive_path')
    export._export_archive = mocker.MagicMock(return_value='USB_CONNECTED')

    export._run_usb_test('mock_archive_dir')

    export._export_archive.assert_called_once_with('mock_archive_path')
    export._create_archive.assert_called_once_with(
        'mock_archive_dir', 'usb-test.sd-export', {'device': 'usb-test'})


def test__run_usb_test_raises_ExportError_if_not_USB_CONNECTED(mocker):
    '''
    Ensure ExportError is raised if _run_disk_test returns anything other than 'USB_CONNECTED'.
    '''
    export = Export()
    export._create_archive = mocker.MagicMock(return_value='mock_archive_path')
    export._export_archive = mocker.MagicMock(return_value='SOMETHING_OTHER_THAN_USB_CONNECTED')

    with pytest.raises(ExportError):
        export._run_usb_test('mock_archive_dir')


def test__create_archive(mocker):
    '''
    Ensure _create_archive creates an archive in the supplied directory.
    '''
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir:
        archive_path = export._create_archive(temp_dir, 'mock.sd-export', {})
        assert archive_path == os.path.join(temp_dir, 'mock.sd-export')
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_an_export_file(mocker):
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir, NamedTemporaryFile() as export_file:
        archive_path = export._create_archive(temp_dir, 'mock.sd-export', {}, [export_file.name])
        assert archive_path == os.path.join(temp_dir, 'mock.sd-export')
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__create_archive_with_multiple_export_files(mocker):
    '''
    Ensure an archive
    '''
    export = Export()
    archive_path = None
    with TemporaryDirectory() as temp_dir, \
        NamedTemporaryFile() as export_file_one, \
        NamedTemporaryFile() as export_file_two:  # noqa
        archive_path = export._create_archive(
            temp_dir, 'mock.sd-export', {}, [export_file_one.name, export_file_two.name])
        assert archive_path == os.path.join(temp_dir, 'mock.sd-export')
        assert os.path.exists(archive_path)  # sanity check

    assert not os.path.exists(archive_path)


def test__export_archive(mocker):
    '''
    Ensure the subprocess call returns the expected output.
    '''
    mocker.patch('subprocess.check_output', return_value=b'mock')
    export = Export()
    status = export._export_archive('mock.sd-export')

    assert status == 'mock'


def test__export_archive_does_not_raise_ExportError_when_CalledProcessError(mocker):
    '''
    Ensure ExportError is raised if a CalledProcessError is encountered.
    '''
    mock_error = subprocess.CalledProcessError('mock_cmd', 123)
    mocker.patch('subprocess.check_output', side_effect=mock_error)

    export = Export()

    with pytest.raises(ExportError, match='CALLED_PROCESS_ERROR'):
        export._export_archive('mock.sd-export')


def test__export_archive_with_evil_command(mocker):
    '''
    Ensure shell command is shell-escaped.
    '''
    export = Export()
    check_output = mocker.patch('subprocess.check_output', return_value=b'')

    export._export_archive('somefile; rm -rf ~')

    check_output.assert_called_once_with(
        ['qvm-open-in-vm', 'sd-export-usb', "'somefile; rm -rf ~'", '--view-only'], stderr=-2)
