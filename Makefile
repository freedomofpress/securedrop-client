install:
	pipenv install
	cp qubes/securedrop.Proxy /etc/qubes-rpc/securedrop.Proxy

test:
	pipenv run python -m unittest -v
