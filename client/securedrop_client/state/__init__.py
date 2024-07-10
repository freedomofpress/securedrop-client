# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022‒2023 The Freedom of the Press Foundation.
"""
The internal state of the SecureDrop Client.
"""
# Import classes here to make possible to import them from securedrop_client.state
from .domain import ConversationId, File, FileId, SourceId  # noqa: F401
from .state import State  # noqa: F401
