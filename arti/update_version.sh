#!/bin/bash

export DEBEMAIL=securedrop@freedom.press
export DEBFULLNAME="SecureDrop Team"

dch --distribution unstable -v "$1" "New Arti build"
