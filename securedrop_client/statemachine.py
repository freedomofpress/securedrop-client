from functools import partial

class StateMachineMixin:
    def __getattribute__(self, item):
        try:
            return super(StateMachineMixin, self).__getattribute__(item)
        except AttributeError:
            if item in self.machine.events:
                return partial(self.machine.events[item].trigger, self)
            raise