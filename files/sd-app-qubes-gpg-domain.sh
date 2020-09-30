if [ "$(qubesdb-read /name)" = "sd-app" ]; then export QUBES_GPG_DOMAIN="sd-gpg" && sudo aa-enforce /usr/bin/securedrop-client; fi
