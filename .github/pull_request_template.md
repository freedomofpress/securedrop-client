## Description

Fixes #issue.

## Test Plan

- [ ] Confirm that the CI jobs are successful

## How to create a useful test plan

### Qubes OS environment

If these changes modify code paths involving cryptography, the opening of files in VMs or network traffic (via the RPC service), Qubes OS testing in the staging environment is required. For fine tuning of the graphical user interface, testing in any environment in Qubes OS is required. Please make sure you mention it in the **test plan**.

### AppArmor profile

If these changes add or remove files other than client code, the AppArmor profile may need to be updated. Please make sure you mention it in the **test plan**.

### Database migrations

If these changes modify the database schema, you should include a [self-contained] database migration. Testing that the migration applies cleanly on the `main` branch is necessary. Please make sure you mention it in the **test plan**.

  [self-contained]: https://github.com/freedomofpress/securedrop-client#generating-and-running-database-migrations
