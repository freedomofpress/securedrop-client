from PyQt5.QtWidgets import QApplication, QWidget, QVBoxLayout
from reactive_qt.layout_manager import StatefulReactiveQtAppWindow
import sys

sys.path.append("..")

from qframe import render, app, state

import spot.system
import time

import layout
import actors
# import db

# Our qframe app, just holds on to the root of our component tree, and
# provides a callback for the db when it changes.
rapp = app.App()
rapp.set_top(layout.sd_client_app)

login_rapp = app.App()
login_rapp.set_top(layout.login_app)

# Qt boilerplate for app initialization
qapp = QApplication([])

# This will be the element that'll hold our entire UI
vbox = QVBoxLayout()
login_vbox = QVBoxLayout()

# Initialize our stateful UI handler with the current UI and the dict
# of element IDs to Qt object (both just hold the empty container
# element)
appwindow = StatefulReactiveQtAppWindow({'id': 'container',
                                         'contains': []},
                                        {'container': (vbox,)})

login_appwindow = StatefulReactiveQtAppWindow({'id': 'login-container',
                                               'contains': []},
                                              {'login-container': (login_vbox,)})

# When the local db updates and we have a new rendered UI description,
# tell the stateful UI handler about it.
#
# This callback ends up getting run in an arbitrary thread. We don't
# want that: we want it to run in the UI thread, at least the bits
# which may make new Qt bits. We use Qt's signals and slots to
# facilitate this.
rapp.update_cb = lambda x: appwindow.layout_changed.emit(x)
login_rapp.update_cb = lambda x: login_appwindow.layout_changed.emit(x)

# Set Qt widget's initial layout (an empty vbox)
appwindow.setLayout(vbox)
login_appwindow.setLayout(login_vbox)

# We're going to define the logic of our application in a small actor
# system.
system = spot.system.ActorSystem(qapp)

# And tell our application what to do when any UI action happens:
# place it in the `event` actor
rapp.event_cb = lambda event: system.tell('event', event)
login_rapp.event_cb = lambda event: system.tell('event', event)

# initialize db with state
db = state.DB([rapp, login_rapp], layout.app_state)

system.create_actor(actors.DBUpdater(db), 'updater')
system.create_actor(actors.EventCatcher(), 'event')
system.create_actor(actors.APIMultiplexer(), 'api-multiplexer')
system.create_actor(actors.Receiver(), 'api-receiver')
system.create_actor(actors.LoginResult(login_appwindow), 'login-result')

# kick off the actor network
# system.tell('timer','click')

# show the UI
appwindow.show()
login_appwindow.show()
qapp.exec_()
