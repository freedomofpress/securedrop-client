#!/usr/bin/env python3
import sys

from securedrop_client.models import Base, make_engine
Base.metadata.create_all(make_engine(sys.argv[1]))
