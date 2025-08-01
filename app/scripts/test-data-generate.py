#!/usr/bin/env python3
# flake8: noqa: E501
"""
This script generates random test data and overwrites `src/test-data.sql`.
"""

import json
import os
import secrets
import sys
import uuid
from datetime import datetime, timedelta

# Randomly generated plaintext data
SENTENCES = [
    "In pharetra tincidunt urna, non eleifend leo malesuada eu. Nunc.",
    "Mauris eu ante lorem. Nulla eu felis condimentum, iaculis ex.",
    "Vestibulum et cursus nisi. Nam purus ante, interdum in est.",
    "Etiam eros odio, lacinia ut finibus nec, gravida vel lectus.",
    "Donec nec dignissim augue. Nulla sollicitudin nibh nibh, at commodo.",
    "Integer purus massa, congue quis ipsum eget, pellentesque malesuada risus.",
]
PARAGRAPHS = [
    "Nam sem massa, imperdiet ut fringilla molestie, mattis vitae eros. Duis vel odio maximus, rutrum ex id, vestibulum mauris. Duis tristique tincidunt ante, venenatis volutpat quam facilisis ac. Quisque at sem est. Cras posuere leo est, in cursus odio convallis molestie. Donec ex massa, congue eu purus eget, fringilla aliquam metus. Sed in mauris a libero hendrerit ultricies.",
    "Donec ut semper eros. Integer ut mauris mauris. Donec eget eleifend tellus. Praesent commodo felis pellentesque lobortis posuere. Praesent nisl diam, pulvinar ac arcu in, auctor hendrerit quam. Duis quis suscipit magna. Suspendisse et scelerisque massa. In vitae tortor vitae lacus feugiat dignissim in non enim. Praesent lobortis dapibus posuere. Donec vitae elit felis.",
    "Aliquam erat volutpat. Sed congue nec massa eget facilisis. Etiam dui dolor, commodo a urna at, euismod placerat nisi. Cras convallis nibh arcu. Aenean elementum nisi quis lorem fermentum, vel auctor sem faucibus. Nullam mollis posuere ligula ac molestie. Nunc facilisis ornare tincidunt. Nunc commodo dui id bibendum rhoncus. Mauris pretium lacus mi, pulvinar imperdiet ipsum viverra et.",
    "In leo lorem, tincidunt egestas convallis ut, faucibus sit amet lectus. Suspendisse malesuada placerat lectus in tempor. Vestibulum ante ipsum primis in faucibus orci luctus et ultrices posuere cubilia curae; Morbi congue lacus sed purus eleifend, ut sagittis lectus varius. Etiam lacus dolor, blandit sed eros ut, tempor lacinia massa. Vivamus dictum et tortor vehicula suscipit.",
    "Praesent fermentum quam vel ex facilisis egestas. In est velit, malesuada ac efficitur eget, euismod ac velit. Proin tortor ante, dictum et pulvinar eu, tempus ut nibh. Morbi semper sapien arcu. Interdum et malesuada fames ac ante ipsum primis in faucibus. Nullam cursus ante dignissim, vulputate orci a, posuere eros. Vestibulum hendrerit ante magna, at elementum massa rutrum ac.",
    "Curabitur vitae fringilla urna. Nulla sit amet vulputate turpis, nec mollis arcu. Maecenas turpis erat, efficitur in lobortis sit amet, suscipit eu elit. Vestibulum in interdum justo, sed ultrices ligula. Praesent nulla diam, ultricies et metus sit amet, vulputate bibendum nunc. Ut sed libero a dolor vulputate vestibulum quis posuere augue.",
    "Sed bibendum magna eu consectetur congue. Curabitur eu felis ipsum. Phasellus euismod interdum quam et lacinia. Maecenas tellus orci, interdum in enim eu, egestas commodo eros. Fusce aliquam augue nec augue porta imperdiet. Proin eget consectetur risus, ac sollicitudin sapien. Ut ac urna sed purus interdum blandit eget et est. Vivamus convallis lacinia elementum.",
    "Nullam blandit massa neque, sit amet tristique odio imperdiet eget. Pellentesque nec massa malesuada, pellentesque risus vitae, varius nulla. Proin feugiat mattis ultricies. Nunc ut lacinia sem, ut ultricies lectus. Duis vitae lobortis eros. Proin convallis, nisi at imperdiet condimentum, arcu mauris tincidunt orci, ac tristique erat nunc eget felis. Donec tempor nisl nibh, a commodo mi luctus ut.",
    "Phasellus ultrices cursus neque at ultrices. Fusce congue suscipit odio id sodales. Maecenas mollis sodales justo, vel dignissim sapien bibendum sit amet. Duis lorem lacus, sodales ut sagittis vitae, tincidunt vel lectus. Vestibulum sed efficitur nulla. Vivamus eu purus sit amet nisi porta consequat ac ac turpis.",
    "Curabitur suscipit arcu eu mi porttitor, a varius massa commodo. Etiam lacinia at nulla sed fringilla. Curabitur et bibendum arcu, ac tincidunt velit. In feugiat, turpis nec congue pellentesque, purus risus sollicitudin nisl, nec vestibulum enim libero quis augue. Duis id accumsan eros.",
]


if len(sys.argv) != 3:
    print(f"Usage: {sys.argv[0]} <securedrop_repo_path> <count>")
    sys.exit(1)

securedrop_repo_path = sys.argv[1]
count = int(sys.argv[2])

adjectives_filename = os.path.join(
    securedrop_repo_path, "securedrop", "dictionaries", "adjectives.txt"
)
nouns_filename = os.path.join(securedrop_repo_path, "securedrop", "dictionaries", "nouns.txt")

with open(adjectives_filename) as f:
    adjectives = [line.strip() for line in f if line.strip()]
with open(nouns_filename) as f:
    nouns = [line.strip() for line in f if line.strip()]


def random_plaintext():
    """Generate a random plaintext string."""
    plaintext = ""
    if secrets.choice([True, False]):
        # Choose 1 to 3 sentences
        num_sentences = secrets.randbelow(3) + 1
        sentences = [secrets.choice(SENTENCES) for _ in range(num_sentences)]
        plaintext = " ".join(sentences)
    else:
        # Choose 1 to 3 paragraphs
        num_paragraphs = secrets.randbelow(3) + 1
        paragraphs = [secrets.choice(PARAGRAPHS) for _ in range(num_paragraphs)]
        plaintext = "\n\n".join(paragraphs)

    # Randomly, add some emoji and unicode characters to the end
    if secrets.choice([True, False]):
        special_chars = [
            "😀",
            "🚀",
            "✨",
            "🔥",
            "💡",
            "🎉",
            "🌍",
            "📝",
            "🍀",
            "💻",
            "Ω",
            "λ",
            "π",
            "ß",
            "ø",
            "ç",
            "漢字",
            "ありがとう",
            "😊",
            "🌟",
        ]
        plaintext += (
            f"\n\n<p>Random content with special characters: {secrets.choice(special_chars)}</p>"
        )
    return plaintext


def random_fingerprint():
    return "".join(secrets.choice("0123456789ABCDEF") for _ in range(40))


def random_public_key(fingerprint):
    return f"-----BEGIN PGP PUBLIC KEY BLOCK-----\\nComment: {fingerprint}\\n-----END PGP PUBLIC KEY BLOCK-----"


def random_date_within_last_year():
    now = datetime.now()
    days_ago = secrets.randbelow(365)
    seconds_ago = secrets.randbelow(86401)
    dt = now - timedelta(days=days_ago, seconds=seconds_ago)
    return dt.isoformat()


def random_journalist_designation():
    return f"{secrets.choice(adjectives)} {secrets.choice(nouns)}"


def escape_sql_string(s):
    return s.replace("'", "''")


def insert(table, data):
    columns = ", ".join(escape_sql_string(str(col)) for col in data)
    values = []
    for value in data.values():
        if isinstance(value, dict):
            value = json.dumps(value)
        values.append(f"'{escape_sql_string(str(value))}'")
    return f"INSERT INTO {escape_sql_string(str(table))} ({columns}) VALUES ({', '.join(values)});"  # noqa: S608


sql_lines = []

# Generate sources
for _ in range(count):
    # Start with a UUID
    source_uuid = str(uuid.uuid4())
    has_attachment = secrets.choice([True, False])

    # Generate items for this source
    item_rows = []
    num_items = secrets.randbelow(20) + 1
    for i in range(num_items):
        item_uuid = str(uuid.uuid4())
        if i == 0:
            kind = "message"
        elif has_attachment:
            kind = secrets.choice(["message", "file", "reply"])
        else:
            kind = secrets.choice(["message", "reply"])
        seen_by = [str(uuid.uuid4()) for _ in range(secrets.randbelow(4))]
        size = secrets.randbelow(9991) + 10
        item_obj = {
            "uuid": item_uuid,
            "kind": kind,
            "seen_by": seen_by,
            "size": size,
            "source": source_uuid,
        }
        if kind in ["message", "file"]:
            # 10% chance of being unread (is_read == False)
            item_obj["is_read"] = secrets.randbelow(10) != 0
        if kind == "reply":
            item_obj["is_deleted_by_source"] = secrets.choice([True, False])
        plaintext = random_plaintext()
        filename = f"file_{secrets.randbelow(1000) + 1}.txt" if kind == "file" else None
        item_row = {
            "uuid": item_uuid,
            "data": item_obj,
            "plaintext": plaintext,
            "filename": filename,
        }
        item_rows.append(item_row)

    # Generate source data
    fingerprint = random_fingerprint()
    is_starred = secrets.randbelow(10) == 0
    journalist_designation = random_journalist_designation()
    last_updated = random_date_within_last_year()
    public_key = random_public_key(fingerprint)
    source_obj = {
        "fingerprint": fingerprint,
        "is_starred": is_starred,
        "journalist_designation": journalist_designation,
        "last_updated": last_updated,
        "public_key": public_key,
        "uuid": source_uuid,
    }

    # If any item is unread, set is_read to False
    is_read = True
    for item_row in item_rows:
        if (
            isinstance(item_row["data"], dict)
            and item_row["data"].get("is_read") is not None
            and not item_row["data"].get("is_read", False)
        ):
            is_read = False
            break

    # If any item is a message, set show_message_preview to True
    show_message_preview = False
    for item_row in item_rows:
        if (
            isinstance(item_row["data"], dict)
            and item_row["data"].get("kind") is not None
            and item_row["data"].get("kind", "") == "message"
        ):
            show_message_preview = True
            break

    # The message preview should be the most recent message's plaintext
    message_preview = ""
    for item_row in reversed(item_rows):
        if (
            isinstance(item_row["data"], dict)
            and item_row["data"].get("kind") == "message"
            and item_row.get("plaintext")
        ):
            message_preview = str(item_row.get("plaintext", ""))[:200]  # Limit to 200 characters
            break

    # Create the source row SQL
    source_row = {
        "uuid": source_uuid,
        "data": source_obj,
        "is_read": is_read,
        "has_attachment": has_attachment,
        "show_message_preview": show_message_preview,
        "message_preview": message_preview,
    }
    sql_lines.append(insert("sources", source_row))

    # Create the items SQL
    for item_row in item_rows:
        sql_lines.append(insert("items", item_row))

test_data_path = os.path.abspath(os.path.join(os.path.dirname(__file__), "../src/test-data.sql"))
with open(test_data_path, "w") as f:
    f.write("\n".join(sql_lines) + "\n")
