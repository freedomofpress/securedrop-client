from unittest import mock, TestCase

import securedrop_log


@mock.patch('securedrop_log.Popen')
class TestLogger(TestCase):
    def test_singleton_there_can_be_only_one(self, mock_popen):
        logger1 = securedrop_log.SecureDropLog('name', 'logvmname')
        logger2 = securedrop_log.SecureDropLog('name', 'logvmname')

        self.assertEqual(logger1.qubes_log, logger2.qubes_log)

    def test_singleton_raises_exception_for_dev(self, mock_popen):
        # No exception raised
        securedrop_log.SecureDropLog('name', 'logvmname')

        with self.assertRaises(Exception):
            securedrop_log.SecureDropLog('name2', 'logvmname2')
