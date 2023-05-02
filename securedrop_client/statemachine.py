from functools import partial


class StateMachineMixin:
    """
    Let any class transparently use a static (class-level) state machine,
    rather than running a separate machine per class instance.[1]

    [1]: https://github.com/pytransitions/transitions/blob/f3e01de336d24005b8c4abb012185a89af9727d9/examples/Frequently%20asked%20questions.ipynb
    """

    def __getattribute__(self, item):
        try:
            return super(StateMachineMixin, self).__getattribute__(item)
        except AttributeError:
            if item in self.machine.events:
                return partial(self.machine.events[item].trigger, self)
            raise
