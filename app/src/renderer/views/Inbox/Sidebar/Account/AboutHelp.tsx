import logoImage from "../../../../../../resources/images/logo.png";

// Help Modal Content
function AboutHelp() {

  return (
    <>
      {/* Header band */}
      <div className="bg-[#f3f4f6] px-[28px] py-[24px] flex items-center gap-[20px]">
        {/* Logo */}
        <div className="w-[88px] h-[88px] shrink-0 flex items-center justify-center">
            <img src={logoImage} alt="SecureDrop" />
        </div>

        {/* Header text */}
        <div className="text-[rgba(0,0,0,0.88)]">
          <div className="text-[22px] font-bold leading-[1.2] tracking-[-0.3px]">SecureDrop Client</div>
          <div className="text-[13px] text-[rgba(0,0,0,0.65)] mt-[5px] leading-[1.4]">Secure communications for journalists and sources</div>
        </div>
      </div>

      {/* Body */}
      <div className="p-[20px_28px]">

        {/* Version row */}
        <div className="flex items-center gap-[10px] mb-[16px]">
          <span className="text-[13px] font-semibold text-[#181d27]">Version</span>
          <span className="bg-[#e6f4ff] text-[#1677ff] border border-[#91caff] rounded-[4px] px-[8px] text-[13px] font-semibold leading-[22px]">v0.18.0-rc1</span>
        </div>

        {/* Divider */}
        <div className="h-[1px] bg-[#f0f0f0] mb-[16px]"></div>

        {/* Links - single column */}
        <div className="flex flex-col gap-[8px] mb-[16px]">
          <div className="flex items-start gap-[12px]">
            <span className="text-[13px] text-[#181d27] font-medium w-[140px] shrink-0">Tech support</span>
            <span className="text-[13px] text-[#8c8c8c] break-all">support.freedom.press</span>
          </div>
          <div className="flex items-start gap-[12px]">
            <span className="text-[13px] text-[#181d27] font-medium w-[140px] shrink-0">Documentation</span>
            <span className="text-[13px] text-[#8c8c8c] break-all">docs.securedrop.org</span>
          </div>
          <div className="flex items-start gap-[12px]">
            <span className="text-[13px] text-[#181d27] font-medium w-[140px] shrink-0">Repository</span>
            <span className="text-[13px] text-[#8c8c8c] break-all">github.com/freedomofpress/securedrop-client</span>
          </div>
          <div className="flex items-start gap-[12px]">
            <span className="text-[13px] text-[#181d27] font-medium w-[140px] shrink-0">Security advisories</span>
            <span className="text-[13px] text-[#8c8c8c] break-all">github.com/freedomofpress/securedrop-client/security/advisories</span>
          </div>
        </div>

        {/* Divider */}
        <div className="h-[1px] bg-[#f0f0f0] mb-[16px]"></div>

        {/* License */}
        <p className="text-[12px] text-[#8c8c8c] leading-[1.5]">SecureDrop is open source and released under the GNU Affero General Public License v3.</p>
      </div>

      {/* Footer */}
      <div className="px-[16px] py-[12px] border-t border-[#f0f0f0] flex items-center justify-between gap-[12px]">
        <p className="text-[11px] text-[#8c8c8c] leading-[1.4] max-w-[320px]">
          © 2013–2026 Aaron Swartz, James Dolan, Freedom of the Press Foundation, and SecureDrop contributors
        </p>
      </div>
  </>
  );
}

export default AboutHelp;
