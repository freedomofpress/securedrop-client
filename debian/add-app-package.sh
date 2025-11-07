#!/bin/bash
# Add securedrop-app package definition and its build dependencies to debian/control

set -euo pipefail

# Add nodejs to Build-Depends (includes npm)
sed -i 's/\(Build-Depends:.*\)/\1, nodejs/' debian/control

# Add the securedrop-app package stanza to the end of debian/control
cat >> debian/control <<EOF

Package: securedrop-app
Architecture: any
Depends: \${shlibs:Depends}, \${misc:Depends}
Description: SecureDrop App for journalists
EOF
