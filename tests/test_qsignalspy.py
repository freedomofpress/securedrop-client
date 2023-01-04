import unittest

from PyQt5.QtCore import QObject, pyqtSignal, pyqtSlot
from PyQt5.QtTest import QSignalSpy

from tests.helper import app  # noqa: F401


class Service(QObject):
    """Connects a response signal to a query signal."""

    response = pyqtSignal()

    def __init__(self):
        super().__init__()

    def connect_signals(self, query):
        query.connect(self.response)


class Client(QObject):
    """Emits a query signal."""

    query = pyqtSignal()

    def __init__(self):
        super().__init__()


class TestService(unittest.TestCase):
    def test_assert_wait(self):
        client = Client()
        service = Service()

        response_emissions = QSignalSpy(service.response)
        self.assertTrue(response_emissions.isValid())

        query_emissions = QSignalSpy(client.query)
        self.assertTrue(query_emissions.isValid())

        service.connect_signals(query=client.query)

        client.query.emit()  # Act.
        assert query_emissions.wait(200)
        assert response_emissions.wait(200)
        self.assertEqual(1, len(query_emissions))
        self.assertEqual(1, len(response_emissions))

    def test_wait_without_assert(self):
        client = Client()
        service = Service()

        response_emissions = QSignalSpy(service.response)
        self.assertTrue(response_emissions.isValid())

        query_emissions = QSignalSpy(client.query)
        self.assertTrue(query_emissions.isValid())

        service.connect_signals(query=client.query)

        client.query.emit()  # Act.
        query_emissions.wait(200)
        response_emissions.wait(200)
        self.assertEqual(1, len(query_emissions))
        self.assertEqual(1, len(response_emissions))

    def test_no_wait(self):
        client = Client()
        service = Service()

        response_emissions = QSignalSpy(service.response)
        self.assertTrue(response_emissions.isValid())

        query_emissions = QSignalSpy(client.query)
        self.assertTrue(query_emissions.isValid())

        service.connect_signals(query=client.query)

        client.query.emit()  # Act.
        self.assertEqual(1, len(query_emissions))
        self.assertEqual(1, len(response_emissions))
