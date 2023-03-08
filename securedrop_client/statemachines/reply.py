from statemachine import State, StateMachine


class ReplyStateMachine(StateMachine):
    Pending = State("Pending", initial=True)
    SendPending = State("SendPending")

    send_pending = Pending.to(SendPending)
