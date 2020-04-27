# Description

Fixes #issue.

# Test Plan


# Checklist

If these changes modify code paths involving cryptography, the opening of files in VMs or network (via the RPC service) traffic, Qubes testing in the staging environment is required. For fine tuning of the graphical user interface, testing in any environment in Qubes is required. Please check as applicable:

 - [ ] I have tested these changes in the appropriate Qubes environment
 - [ ] I do not have an appropriate Qubes OS workstation set up (the reviewer will need to test these changes)
 - [ ] These changes should not need testing in Qubes

If these changes add or remove files other than client code, the AppArmor profile may need to be updated. Please check as applicable:

 - [ ] I have updated the [AppArmor profile](https://github.com/freedomofpress/securedrop-client/blob/master/files/usr.bin.securedrop-client)
 - [ ] No update to the AppArmor profile is required for these changes
 - [ ] I don't know and would appreciate guidance

If these changes modify the database schema, you should include a database migration. Please check as applicable:

 - [ ] I have written a migration and upgraded a test database based on `master` and confirmed that the migration applies cleanly
 - [ ] I have written a migration but have not upgraded a test database based on `master` and would like the reviewer to do so
 - [ ] I need help writing a database migration
 - [ ] No database schema changes are needed
