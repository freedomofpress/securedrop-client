from qframe.components import component
from qframe.subscriptions import subscribes
from securedrop_client.resources import path

# db

app_state = { 'sources': [{'name': 'avro vulcan',
                           'starred': True,
                           'updated': "2018-12-18",
                           'snippet': "This airplane is about to be grounded for ever."},
                          {'name': 'twin beech',
                           'starred': False,
                           'updated': "2018-12-17",
                           'snippet': "If one engine fails, you still have other to get you to the site of the crash."},
],
              'conversation': [{'type': 'message',
                                'content': "It is a message",
                                'id': "msg-0"},
                               {'type': 'reply',
                                'content': "It is a reply",
                                'id': "msg-1"},
                               {'type': 'reply',
                                'content': "It is a another reply",
                                'id': "msg-2"},
                               {'type': 'message',
                                'content': "And another message",
                                'id': "msg-3"} ],
              'current-user': None,
              'view': None,
              'login': {
                  'new-user-text': "Cool",
                  'new-password-text': "Cool",
                  'new-tfa-text': "274611",
                  'error': ""
              },
}

# subs

subscriptions = { 'sources': ['sources'],
                  'current-user': ['current-user'],
                  'view': ['view'],
                  'conversation': ['conversation'],
                  'new-user-text': ['login', 'new-user-text'],
                  'new-password-text': ['login', 'new-password-text'],
                  'new-tfa-text': ['login', 'new-tfa-text'],
                  'login-error-text': ['login', 'error'],
}

# layout

@component
@subscribes(['current-user'], subscriptions)
def login(subs):
    if subs['current-user'] is None:
        return ['pushbutton/login',
                {'on-click': ("login-clicked")},
                "Log in"]

    return ['pushbutton/login',
            {'on-click': ("login-clicked")},
            "Log out"]

@component
@subscribes(['current-user'], subscriptions)
def userstate(subs):
    if subs['current-user'] is None:
        return ['label/current-user-label',
                {},
                "Signed out"]

    return ['label/current-user-label',
                   {},
                   subs['current-user']]

@component
@subscribes([], subscriptions)
def refresh(subs):
    return ['pushbutton/refresh',
            {'on-click': ("refresh-clicked")},
            "Refresh"]

@component
@subscribes([], subscriptions)
def logo(subs):
    return ['label/logo-label',
                   {},
                   "SecureDrop Client"]

@component
@subscribes([], subscriptions)
def toolbar(subs):
    return ['hbox/toolbar-hbox',
            ['logo/logo', {}],
            ['stretch/logo-stretch', {}],
            ['userstate/user-state', {}],
            ['login/toolbar-login', {}],
            ['refresh/toolbar-refresh', {}]]

def source(s):
    name = s['name']
    starred = s['starred']
    updated = s['updated']

    id = str.join("-", name.split())

    if starred:
        star_source = "star_on.svg"
    else:
        star_source = "star_off.svg"

    return ['vbox', {'id': "source-container-" + id},
            ['hbox', {'id': "source-summary-" + id},
             ['label', {'id': "source-name-" + id},
              "<strong>{}</strong>".format(name)],
             ['stretch', {'id': "source-stretch-" + id}],
             ['svg', {'id': "source-attached-svg-" + id,
                      'source': path("paperclip.svg"),
                      'max-size': (16, 16)}],
             ['svg', {'id': "source-delete-svg-" + id,
                      'source': path("cross.svg"),
                      'max-size': (16, 16)}],
             ['svg', {'id': "source-starred-svg-" + id,
                      'source': path(star_source),
                      'max-size': (16, 16)}]],
            ['label', {'id': "source-updated-" + id}, updated]]

def speech_bubble(id, content, type):
    # XXX margins- see widgets.py
    # XXX other CSS?

    css = "background: #eee; padding: 10px; border: 1px solid #999; border-radius: 20px; "
    if type == "message":
        css += 'border-bottom-right-radius: 0px;'
    else:
        css += 'border-bottom-left-radius: 0px;'

    r = ['vbox', {'id': "speech-bubble-" + id},
         ['label', {'id': "speech-content-" + id,
                    'style': css,
                    'stretch': 6},
          content]]

    return r

def conversation_widget(c):
    type = c['type']
    content = c['content']
    id = c['id']

    box = ['hbox', {'id': "conv-hbox-" + id}]

    if type == 'message':
        box.append(['stretch', {'id': "msg-space-" + id,
                                'stretch-val': 5}])

    box.append(speech_bubble(id, content, type))

    if type == 'reply':
        box.append(['stretch', {'id': "msg-space-" + id,
                                'stretch-val': 5}])
    return box

    # return ['widget', {'id': 'message-widget-' + id,
    #                    'style': "background-color: #eee;"},
    #         box]

@component
@subscribes(['sources'], subscriptions)
def source_list(subs):

    source_container = ['vbox/source-list-vbox', {}]

    for s in subs['sources']:
        source_container.append(source(s))

    return source_container


@component
@subscribes(['conversation'], subscriptions)
def conversation(subs):

    c = ['vbox/conversation-vbox', {}]

    for msg in subs['conversation']:
        c.append(conversation_widget(msg))

    return ['widget/conv-container',
            {'stretch': 6,
             'style': "background-color: #fff;"},
            c]

@component
@subscribes([], subscriptions)
def mainview(subs):

    return ['hbox/main-container',
            ['widget/main-left-column-container', {'stretch': 2},
             ['vbox/main-left-column', {'alignment': 'top'},
              ['label/status', {}, "Waiting to refresh..."],
              ['label/error-status', {}, ""],
              ['source_list/source-list', {}],
             ]],
            ['conversation/conversation', {}]]

@component
@subscribes(['view'], subscriptions)
def sd_client_app(subs):
    return ['vbox/container',
            ['toolbar/toolbar', {'stretch': 1}],
            ['mainview/mainview', {'stretch': 6}]]


# LOGIN APP
@component
@subscribes(['new-user-text'], subscriptions)
def username_input(subs):
    return ['lineedit/username-lineedit',
            {'on-edit': 'username-changed'},
            str(subs['new-user-text'])]

@component
@subscribes(['new-password-text'], subscriptions)
def password_input(subs):
    return ['passwordedit/password-edit',
            {'on-edit': 'password-changed'},
            str(subs['new-password-text'])]

@component
@subscribes(['new-tfa-text'], subscriptions)
def tfa_input(subs):
    return ['lineedit/tfa-lineedit',
            {'on-edit': 'tfa-changed'},
            str(subs['new-tfa-text'])]

@component
@subscribes(['login-error-text'], subscriptions)
def login_error(subs):
    return ['label/login-error-label', {}, subs['login-error-text']]

@component
@subscribes([], subscriptions)
def login_app(subs):
    return ['hbox/login-container', {},
            ['label/login-headline', {}, "<h1>Sign in</h1>"],
            ['vbox/login-form-box',
             ['label/login-instructions', {'wordwrap': True},
              "You may read all documents and messages " +
              "shown here, without signing in. To " +
              "correspond with a Source or to check " +
              "the server for updates, you must sign " +
              "in."],
             ['label/login-username-label', {}, "Username"],
             ['username_input/username-input'],
             ['label/login-password-label', {}, "Password"],
             ['password_input/password-input'],
             ['label/login-tfa-label', {}, "Two-Factor Number"],
             ['tfa_input/tfa-input'],
             ['pushbutton/login-submit',
              {'on-click': 'submit-clicked'},
              "Sign in"]],
            ['login_error/login-error']]
