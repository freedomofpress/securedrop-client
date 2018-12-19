class EventCatcher:
    def act(self, msg, tell, create):
        print("Event!", msg)
        event_key = msg[0]

        if event_key == 'password-changed':
            tell('updater', ['password', msg[1]])

        if event_key == 'username-changed':
            tell('updater', ['username', msg[1]])

        if event_key == 'tfa-changed':
            tell('updater', ['tfa', msg[1]])

        elif event_key == 'submit-clicked':
            tell('updater', ['submit'])


# All database mutations route through this actor
class DBUpdater:
    def __init__(self, db):
        self.db = db

    def act(self, msg, tell, create):
        msg_key = msg[0]

        if msg_key == 'password':
            self.db.assoc_in(['login', 'new-password-text'], msg[1])

        elif msg_key == 'username':
            self.db.assoc_in(['login', 'new-user-text'], msg[1])

        elif msg_key == 'tfa':
            self.db.assoc_in(['login', 'new-tfa-text'], msg[1])


        # elif msg_key == 'submit':
        #     todo_text = self.db.get_in(['new-todo-text'])
        #     todos = self.db.get_in(['todos'])

        #     new_todo_index = self.db.get_in(['todo-id'])

        #     todos.append({'id': str(new_todo_index),
        #                   'text': todo_text})

        #     self.db.assoc_in(['todos'], todos)
        #     self.db.assoc_in(['new-todo-text'], "")
        #     self.db.assoc_in(['todo-id'], new_todo_index + 1)
