from securedrop_client.logic import Controller


class Device:
    def __init__(self, controller: Controller) -> None:
        super().__init__()

        self._controller = controller
