import pytest

from securedrop_client.gui.base.progress import FileDownloadProgressBar


@pytest.fixture
def mock_monotonic(mocker):
    """Allow us to manually advance time.monotonic(), which is used for calculating speed"""

    class MockTime:
        current_time = 1000.0

        @classmethod
        def mock_monotonic(cls):
            return cls.current_time

        @classmethod
        def increment(cls, seconds=1.0):
            cls.current_time += seconds
            return cls.current_time

    # Patch time.monotonic with our mock function
    mocker.patch("time.monotonic", side_effect=MockTime.mock_monotonic)
    return MockTime


def test_progress(mock_monotonic):
    widget = FileDownloadProgressBar(100_000_000)
    # Disable the timers as we manually control time
    widget.speed_timer.stop()
    widget.display_timer.stop()
    # At first the progress bar displays "%p" (current value) plus a literal "%"
    assert widget.format() == "%p%"
    # after two speed timer ticks, it should now take over display formatting
    widget.update_speed()
    widget.update_speed()
    widget.update_display()
    # The progress bar should now display calculated percentage
    assert widget.format() == "0%"
    # Add some data and move forward one second
    widget.proxy().set_value(1_000_000)
    mock_monotonic.increment()
    widget.update_speed()
    widget.update_display()
    assert widget.format() == "1% | 292KB/s"

    # Again
    widget.proxy().set_value(2_000_000)
    mock_monotonic.increment()
    widget.update_speed()
    widget.update_display()
    assert widget.format() == "2% | 498KB/s"

    # A lot of data at once
    widget.proxy().set_value(99_000_000)
    mock_monotonic.increment()
    widget.update_speed()
    widget.update_display()
    assert widget.format() == "99% | 28MB/s"

    # 99.99999% does not round to 100%
    widget.proxy().set_value(99_999_999)
    mock_monotonic.increment()
    widget.update_speed()
    widget.update_display()
    assert widget.format() == "99% | 20MB/s"

    # 100% has no speed
    widget.proxy().set_value(100_000_000)
    widget.update_speed()
    widget.update_display()
    assert widget.format() == "100%"

    # Switch to indetermininate mode as we decrypt
    widget.proxy().set_decrypting()
    # maximum() == 0 is what defines indeterminate mode
    assert widget.maximum() == 0
