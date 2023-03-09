# Copyright (c) 2021-present bigbag/sqlalchemy-state-machine authors and
# contributors.
# 
# SPDX-License-Identifier: Apache-2.0

import typing as t
from dataclasses import dataclass

from transitions import Machine


@dataclass
class StateConfig:
    initial: t.Any
    states: t.List[t.Any]
    transitions: t.Optional[t.List[t.List[t.Any]]]
    state_attribute: t.Optional[str] = "state"
    status_attribute: t.Optional[str] = "status"
    machine_name: t.Optional[str] = "machine"
    after_state_change: t.Optional[t.Any] = None


@dataclass
class StateMixin:
    state_config: StateConfig

    @property
    def state(self):
        return getattr(self, self.state_config.status_attribute)

    @state.setter
    def state(self, value):
        setattr(self, self.state_config.status_attribute, value)

    @classmethod
    def init_state_machine(cls, obj, *args, **kwargs):
        machine = Machine(
            model=obj,
            states=cls.state_config.states,
            transitions=cls.state_config.transitions,
            initial=getattr(obj, obj.state_config.status_attribute) or cls.state_config.initial,
            model_attribute=cls.state_config.state_attribute,
            after_state_change=cls.state_config.after_state_change,
        )

        setattr(obj, cls.state_config.machine_name, machine)