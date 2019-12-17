# Description

Fixes #issue.

# Test Plan


# Checklist

If these changes modify code paths involving cryptography, the opening of files in VMs or network (via the RPC service) traffic, Qubes testing in the staging environment is required. For fine tuning of the graphical user interface, testing in any environment in Qubes is required. Please check as applicable:

 - [ ] I have tested these changes in the appropriate Qubes environment
 - [ ] I do not have an appropriate Qubes OS workstation set up (the reviewer will need to test these changes)
 - [ ] These changes should not need testing in Qubes

 If the client interacts with a new file, or no longer interacts with a file, the AppArmor profile may need to be updated. Please check as applicable:

 - [ ] I have submitted a separate PR for the AppArmor profile update to the [packaging repo](https://github.com/freedomofpress/securedrop-debian-packaging)
 - [ ] No AppArmor profile update is required for these changes
