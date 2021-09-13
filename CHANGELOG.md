Changelog
=========

0.3.2
-----

* Update idna to 3.2 (#169)

0.3.1
-----

* Update urllib3 to 1.26.6 to address CVE-2021-33503 (#166)
* Update certifi to 2021.5.30, idna to 2.8, requests to 2.26.0 (#167)
 
0.3.0
-----

* Support "delete_conversation " endpoint (#158)

0.2.0
-----

* Support "users" endpoint (#134).
* Update urllib3 from 1.25.8 to 1.25.10 (#136).
* Support "seen" endpoint (#140).
* Add "seen_by" as an attribute on the Submission and Reply objects (#140).

0.1.1
-----

* Add journalist name to Reply object (#125).

0.1.0
-----

* Pass timeout value to the proxy (#117).
* Update PyYAML to 5.3.1 (#120).

0.0.13
------

* Bug fix: return RequestTimeoutError and ServerConnectionError exceptions instead of AuthError, no longer raise KeyError when a file fails to download via the proxy (#109)
* Adds test cases and uses pip-tools for development dependency management (#112).

0.0.12
------

* Updates qrexec policy keyword character (#102).
* Expose journalist first and last name through the API (#105).

0.0.11
------

* Expose ETags in submission and reply downloads (#96).
* Update tests and test data for first and last name (#92).
* Bug fix: Ensure RequestTimeoutError is raised for submission and reply downloads (#95).

0.0.10
------

* Support logout endpoint (#88).

0.0.9
-----

* Create a timeout exception to catch all possible timeouts from `requests` / Qubes RPC
* Remove mutable global state for the proxy VM name

0.0.8
-----

* Revert return type of API.authenticate to bool

0.0.7
-----

* Update PyYAML dependency to 5.1

0.0.6
-----

* Fix auth header to user "Token" and not "token" (#56).
* Parse the new required field `filename` in the response when posting a reply (#54).

0.0.5
-----

* Allow clients to set UUID of replies via API (#49).

0.0.4
-----

* Rename default proxy VM from sd-journalist to sd-proxy (#43).
* Get stderr text when using Qubes proxy (#38).
* Parse reply UUID (#42).
* Fix incorrect error message when downloading a file (#36).

0.0.3
-----

* Support UUID-only creation of Replies (#31).

0.0.2
-----

* Support SDK use in a Qubes vault AppVM via securedrop-proxy (#21).
* Add journalist UUID as an attribute on the Reply object (#19).

0.0.1
-----

* Initial alpha release.
