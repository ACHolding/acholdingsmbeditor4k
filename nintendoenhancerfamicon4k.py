#!/usr/bin/env python3
"""
SMB ROMHacking Suite - Tkinter

A lightweight editor for legally obtained Super Mario Bros. (NES) ROMs.
It does not include or download copyrighted ROM data.

Features:
- Open iNES/NES ROM files
- Basic ROM info and checksum view
- Validate common SMB PRG/CHR layout
- Hex editor with address jump/search/patch bytes
- Text/string finder
- Palette viewer/editor for NES color index bytes
- IPS patch create/apply
- Backup before save

Run:
    python smb_romhacking_suite_tkinter.py
"""

from __future__ import annotations

import hashlib
import os
import shutil
import struct
import tkinter as tk
from dataclasses import dataclass
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk


NES_MASTER_PALETTE = [
    "#626262", "#001FB2", "#2404C8", "#5200B2", "#730076", "#800024", "#730B00", "#522800",
    "#244400", "#005700", "#005C00", "#005324", "#003C76", "#000000", "#000000", "#000000",
    "#ABABAB", "#0D57FF", "#4B30FF", "#8A13FF", "#BC08D6", "#D21269", "#C72E00", "#9D5400",
    "#607B00", "#209800", "#00A300", "#009942", "#007DB4", "#000000", "#000000", "#000000",
    "#FFFFFF", "#53AEFF", "#9085FF", "#D365FF", "#FF57FF", "#FF5DCF", "#FF7757", "#FA9E00",
    "#BDC700", "#7AE700", "#43F611", "#26EF7E", "#2CD5F6", "#4E4E4E", "#000000", "#000000",
    "#FFFFFF", "#B6E1FF", "#CED1FF", "#E9C3FF", "#FFC0FF", "#FFC3E8", "#FFCCCC", "#FFD9A7",
    "#E9E681", "#CEF481", "#B6FB9A", "#A9FAC3", "#A9F0F4", "#B8B8B8", "#000000", "#000000",
]

# SMB is commonly 16KB PRG + 8KB CHR. iNES header is 16 bytes.
COMMON_SMB_SHA1 = {
    # Values differ across dumps/revisions/headers; use as hints only.
}


@dataclass
class NESHeader:
    prg_banks: int
    chr_banks: int
    mapper: int
    mirroring: str
    battery: bool
    trainer: bool
    four_screen: bool

    @property
    def prg_size(self) -> int:
        return self.prg_banks * 16 * 1024

    @property
    def chr_size(self) -> int:
        return self.chr_banks * 8 * 1024


class ROMModel:
    def __init__(self) -> None:
        self.path: Path | None = None
        self.data = bytearray()
        self.header: NESHeader | None = None

    def load(self, path: str | Path) -> None:
        p = Path(path)
        raw = p.read_bytes()
        if len(raw) < 16 or raw[:4] != b"NES\x1a":
            raise ValueError("Not a valid iNES/NES ROM: missing NES header.")
        self.path = p
        self.data = bytearray(raw)
        self.header = self.parse_header(raw)

    @staticmethod
    def parse_header(raw: bytes) -> NESHeader:
        flags6 = raw[6]
        flags7 = raw[7]
        mapper = (flags6 >> 4) | (flags7 & 0xF0)
        mirroring = "Vertical" if (flags6 & 1) else "Horizontal"
        return NESHeader(
            prg_banks=raw[4],
            chr_banks=raw[5],
            mapper=mapper,
            mirroring=mirroring,
            battery=bool(flags6 & 0x02),
            trainer=bool(flags6 & 0x04),
            four_screen=bool(flags6 & 0x08),
        )

    def save(self, path: str | Path | None = None, backup: bool = True) -> None:
        target = Path(path) if path else self.path
        if target is None:
            raise ValueError("No save path selected.")
        if backup and target.exists():
            backup_path = target.with_suffix(target.suffix + ".bak")
            shutil.copy2(target, backup_path)
        target.write_bytes(self.data)
        self.path = target

    def sha1(self) -> str:
        return hashlib.sha1(bytes(self.data)).hexdigest()

    def md5(self) -> str:
        return hashlib.md5(bytes(self.data)).hexdigest()

    def crc32(self) -> str:
        import zlib
        return f"{zlib.crc32(bytes(self.data)) & 0xFFFFFFFF:08X}"

    def read(self, offset: int, length: int) -> bytes:
        return bytes(self.data[offset:offset + length])

    def write(self, offset: int, blob: bytes) -> None:
        if offset < 0 or offset + len(blob) > len(self.data):
            raise ValueError("Write is outside ROM bounds.")
        self.data[offset:offset + len(blob)] = blob

    @property
    def data_start(self) -> int:
        if self.header and self.header.trainer:
            return 16 + 512
        return 16

    @property
    def chr_start(self) -> int:
        if not self.header:
            return 0
        return self.data_start + self.header.prg_size


class IPS:
    @staticmethod
    def create(original: bytes, modified: bytes) -> bytes:
        if len(original) != len(modified):
            raise ValueError("IPS creation requires files of equal length in this editor.")
        out = bytearray(b"PATCH")
        i = 0
        n = len(original)
        while i < n:
            if original[i] == modified[i]:
                i += 1
                continue
            start = i
            chunk = bytearray()
            while i < n and original[i] != modified[i] and len(chunk) < 0xFFFF:
                chunk.append(modified[i])
                i += 1
            if start > 0xFFFFFF:
                raise ValueError("IPS only supports offsets up to 0xFFFFFF.")
            out.extend(start.to_bytes(3, "big"))
            out.extend(len(chunk).to_bytes(2, "big"))
            out.extend(chunk)
        out.extend(b"EOF")
        return bytes(out)

    @staticmethod
    def apply(base: bytes, patch: bytes) -> bytes:
        if not patch.startswith(b"PATCH"):
            raise ValueError("Invalid IPS patch: missing PATCH header.")
        data = bytearray(base)
        i = 5
        while i < len(patch):
            if patch[i:i + 3] == b"EOF":
                return bytes(data)
            if i + 5 > len(patch):
                raise ValueError("Truncated IPS patch.")
            offset = int.from_bytes(patch[i:i + 3], "big")
            size = int.from_bytes(patch[i + 3:i + 5], "big")
            i += 5
            if size == 0:
                if i + 3 > len(patch):
                    raise ValueError("Truncated IPS RLE record.")
                rle_size = int.from_bytes(patch[i:i + 2], "big")
                value = patch[i + 2]
                i += 3
                end = offset + rle_size
                if end > len(data):
                    data.extend(b"\x00" * (end - len(data)))
                data[offset:end] = bytes([value]) * rle_size
            else:
                if i + size > len(patch):
                    raise ValueError("Truncated IPS record.")
                end = offset + size
                if end > len(data):
                    data.extend(b"\x00" * (end - len(data)))
                data[offset:end] = patch[i:i + size]
                i += size
        raise ValueError("Invalid IPS patch: missing EOF.")


class HexView(ttk.Frame):
    def __init__(self, master: tk.Widget, app: "SMBEditorApp") -> None:
        super().__init__(master)
        self.app = app
        self.offset_var = tk.StringVar(value="0x000000")
        self.bytes_per_page = 0x400

        top = ttk.Frame(self)
        top.pack(fill="x", padx=6, pady=6)
        ttk.Label(top, text="Offset:").pack(side="left")
        ttk.Entry(top, textvariable=self.offset_var, width=12).pack(side="left", padx=4)
        ttk.Button(top, text="Go", command=self.refresh).pack(side="left")
        ttk.Button(top, text="Patch bytes", command=self.patch_bytes).pack(side="left", padx=4)
        ttk.Button(top, text="Find hex", command=self.find_hex).pack(side="left", padx=4)
        ttk.Button(top, text="Find text", command=self.find_text).pack(side="left", padx=4)

        self.text = tk.Text(self, wrap="none", font=("Courier New", 10), height=28)
        y = ttk.Scrollbar(self, orient="vertical", command=self.text.yview)
        x = ttk.Scrollbar(self, orient="horizontal", command=self.text.xview)
        self.text.configure(yscrollcommand=y.set, xscrollcommand=x.set)
        self.text.pack(side="left", fill="both", expand=True)
        y.pack(side="right", fill="y")
        x.pack(side="bottom", fill="x")

    def parse_offset(self) -> int:
        s = self.offset_var.get().strip().lower()
        return int(s, 16) if s.startswith("0x") else int(s)

    def refresh(self) -> None:
        rom = self.app.rom
        self.text.delete("1.0", "end")
        if not rom.data:
            self.text.insert("end", "Open a ROM first.\n")
            return
        try:
            offset = max(0, min(self.parse_offset(), len(rom.data) - 1))
        except Exception:
            messagebox.showerror("Bad offset", "Offset must be decimal or hex, e.g. 0x10.")
            return
        end = min(len(rom.data), offset + self.bytes_per_page)
        for row in range(offset, end, 16):
            chunk = rom.read(row, min(16, end - row))
            hex_part = " ".join(f"{b:02X}" for b in chunk)
            asc = "".join(chr(b) if 32 <= b <= 126 else "." for b in chunk)
            self.text.insert("end", f"{row:06X}: {hex_part:<47}  {asc}\n")

    def patch_bytes(self) -> None:
        if not self.app.ensure_rom():
            return
        off_s = simpledialog.askstring("Patch bytes", "ROM offset, decimal or hex:", initialvalue=self.offset_var.get())
        if not off_s:
            return
        data_s = simpledialog.askstring("Patch bytes", "Bytes as hex, e.g. A9 01 8D 00 20:")
        if not data_s:
            return
        try:
            offset = int(off_s, 16) if off_s.lower().startswith("0x") else int(off_s)
            blob = bytes.fromhex(data_s.replace(",", " "))
            self.app.rom.write(offset, blob)
            self.app.mark_dirty()
            self.offset_var.set(f"0x{offset:06X}")
            self.refresh()
        except Exception as exc:
            messagebox.showerror("Patch failed", str(exc))

    def find_hex(self) -> None:
        if not self.app.ensure_rom():
            return
        q = simpledialog.askstring("Find hex", "Hex bytes to find:")
        if not q:
            return
        try:
            needle = bytes.fromhex(q.replace(",", " "))
            pos = bytes(self.app.rom.data).find(needle)
            if pos < 0:
                messagebox.showinfo("Find hex", "Not found.")
            else:
                self.offset_var.set(f"0x{pos:06X}")
                self.refresh()
        except Exception as exc:
            messagebox.showerror("Find failed", str(exc))

    def find_text(self) -> None:
        if not self.app.ensure_rom():
            return
        q = simpledialog.askstring("Find text", "ASCII text to find:")
        if not q:
            return
        pos = bytes(self.app.rom.data).find(q.encode("ascii", "ignore"))
        if pos < 0:
            messagebox.showinfo("Find text", "Not found as plain ASCII. SMB uses many byte tables, not ordinary readable text.")
        else:
            self.offset_var.set(f"0x{pos:06X}")
            self.refresh()


class PaletteEditor(ttk.Frame):
    def __init__(self, master: tk.Widget, app: "SMBEditorApp") -> None:
        super().__init__(master)
        self.app = app
        self.offset_var = tk.StringVar(value="0x000000")
        top = ttk.Frame(self)
        top.pack(fill="x", padx=6, pady=6)
        ttk.Label(top, text="Palette table offset:").pack(side="left")
        ttk.Entry(top, textvariable=self.offset_var, width=12).pack(side="left", padx=4)
        ttk.Button(top, text="Load 32 bytes", command=self.load_palette).pack(side="left")
        ttk.Button(top, text="Write changes", command=self.write_palette).pack(side="left", padx=4)
        ttk.Label(top, text="Tip: find known palette byte sequences in Hex tab first.").pack(side="left", padx=12)

        self.cells: list[tuple[tk.Canvas, tk.StringVar]] = []
        grid = ttk.Frame(self)
        grid.pack(padx=8, pady=8, anchor="nw")
        for i in range(32):
            f = ttk.Frame(grid)
            f.grid(row=i // 8, column=i % 8, padx=5, pady=5)
            c = tk.Canvas(f, width=36, height=24, highlightthickness=1, highlightbackground="#777")
            c.pack()
            var = tk.StringVar(value="00")
            e = ttk.Entry(f, textvariable=var, width=4)
            e.pack()
            e.bind("<KeyRelease>", lambda _e, idx=i: self.update_cell_color(idx))
            self.cells.append((c, var))
        self.refresh_colors()

    def refresh_colors(self) -> None:
        for i in range(len(self.cells)):
            self.update_cell_color(i)

    def update_cell_color(self, idx: int) -> None:
        c, var = self.cells[idx]
        try:
            val = int(var.get().strip(), 16) & 0x3F
            color = NES_MASTER_PALETTE[val]
        except Exception:
            color = "#000000"
        c.delete("all")
        c.create_rectangle(0, 0, 36, 24, fill=color, outline=color)

    def parse_offset(self) -> int:
        s = self.offset_var.get().strip().lower()
        return int(s, 16) if s.startswith("0x") else int(s)

    def load_palette(self) -> None:
        if not self.app.ensure_rom():
            return
        try:
            offset = self.parse_offset()
            blob = self.app.rom.read(offset, 32)
            if len(blob) < 32:
                raise ValueError("Not enough bytes at that offset.")
            for i, b in enumerate(blob):
                self.cells[i][1].set(f"{b & 0x3F:02X}")
            self.refresh_colors()
        except Exception as exc:
            messagebox.showerror("Load palette failed", str(exc))

    def write_palette(self) -> None:
        if not self.app.ensure_rom():
            return
        try:
            offset = self.parse_offset()
            blob = bytes(int(var.get().strip(), 16) & 0x3F for _, var in self.cells)
            self.app.rom.write(offset, blob)
            self.app.mark_dirty()
            messagebox.showinfo("Palette", "Wrote 32 palette bytes.")
        except Exception as exc:
            messagebox.showerror("Write palette failed", str(exc))


class InfoTab(ttk.Frame):
    def __init__(self, master: tk.Widget, app: "SMBEditorApp") -> None:
        super().__init__(master)
        self.app = app
        self.text = tk.Text(self, wrap="word", height=30)
        self.text.pack(fill="both", expand=True, padx=8, pady=8)
        self.refresh()

    def refresh(self) -> None:
        self.text.delete("1.0", "end")
        rom = self.app.rom
        if not rom.data or not rom.header:
            self.text.insert("end", "Open a .nes ROM to begin.\n\nThis tool expects an iNES-format ROM. It does not provide ROM files.\n")
            return
        h = rom.header
        info = [
            f"File: {rom.path}",
            f"Size: {len(rom.data):,} bytes",
            f"SHA1: {rom.sha1()}",
            f"MD5: {rom.md5()}",
            f"CRC32: {rom.crc32()}",
            "",
            "iNES Header",
            f"PRG ROM banks: {h.prg_banks} ({h.prg_size:,} bytes)",
            f"CHR ROM banks: {h.chr_banks} ({h.chr_size:,} bytes)",
            f"Mapper: {h.mapper}",
            f"Mirroring: {h.mirroring}",
            f"Battery-backed RAM: {h.battery}",
            f"Trainer: {h.trainer}",
            f"Four-screen VRAM: {h.four_screen}",
            "",
            "Layout",
            f"PRG start: 0x{rom.data_start:06X}",
            f"CHR start: 0x{rom.chr_start:06X}",
            "",
            "SMB compatibility hints",
        ]
        if h.mapper == 0 and h.prg_banks == 1 and h.chr_banks == 1:
            info.append("Looks like a common NROM-128 SMB-compatible layout.")
        else:
            info.append("This does not look like the common SMB NROM-128 layout. Editing may still work, but offsets may differ.")
        info.append("\nUse IPS patches to share hacks. Do not distribute full ROM files.")
        self.text.insert("end", "\n".join(info))


class PatchTab(ttk.Frame):
    def __init__(self, master: tk.Widget, app: "SMBEditorApp") -> None:
        super().__init__(master)
        self.app = app
        p = ttk.Frame(self)
        p.pack(anchor="nw", padx=12, pady=12)
        ttk.Button(p, text="Create IPS from original + modified", command=self.create_ips).grid(row=0, column=0, sticky="w", pady=4)
        ttk.Button(p, text="Apply IPS to opened ROM", command=self.apply_ips).grid(row=1, column=0, sticky="w", pady=4)
        ttk.Label(p, text="IPS patches are the safer way to distribute ROM hacks.").grid(row=2, column=0, sticky="w", pady=12)

    def create_ips(self) -> None:
        orig = filedialog.askopenfilename(title="Original ROM", filetypes=[("NES ROM", "*.nes"), ("All files", "*.*")])
        if not orig:
            return
        mod = filedialog.askopenfilename(title="Modified ROM", filetypes=[("NES ROM", "*.nes"), ("All files", "*.*")])
        if not mod:
            return
        out = filedialog.asksaveasfilename(title="Save IPS patch", defaultextension=".ips", filetypes=[("IPS patch", "*.ips")])
        if not out:
            return
        try:
            patch = IPS.create(Path(orig).read_bytes(), Path(mod).read_bytes())
            Path(out).write_bytes(patch)
            messagebox.showinfo("IPS", f"Patch saved:\n{out}")
        except Exception as exc:
            messagebox.showerror("IPS create failed", str(exc))

    def apply_ips(self) -> None:
        if not self.app.ensure_rom():
            return
        patch_path = filedialog.askopenfilename(title="Open IPS patch", filetypes=[("IPS patch", "*.ips"), ("All files", "*.*")])
        if not patch_path:
            return
        try:
            patched = IPS.apply(bytes(self.app.rom.data), Path(patch_path).read_bytes())
            self.app.rom.data = bytearray(patched)
            self.app.mark_dirty()
            self.app.refresh_all()
            messagebox.showinfo("IPS", "Patch applied to memory. Save ROM to write it to disk.")
        except Exception as exc:
            messagebox.showerror("IPS apply failed", str(exc))


class SMBEditorApp(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("SMB ROMHacking Suite")
        self.geometry("980x680")
        self.rom = ROMModel()
        self.dirty = False

        self._build_menu()
        self.tabs = ttk.Notebook(self)
        self.info_tab = InfoTab(self.tabs, self)
        self.hex_tab = HexView(self.tabs, self)
        self.palette_tab = PaletteEditor(self.tabs, self)
        self.patch_tab = PatchTab(self.tabs, self)
        self.tabs.add(self.info_tab, text="ROM Info")
        self.tabs.add(self.hex_tab, text="Hex Editor")
        self.tabs.add(self.palette_tab, text="Palette")
        self.tabs.add(self.patch_tab, text="IPS Patches")
        self.tabs.pack(fill="both", expand=True)

        self.status = tk.StringVar(value="Ready")
        ttk.Label(self, textvariable=self.status, anchor="w").pack(fill="x", side="bottom")
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def _build_menu(self) -> None:
        menubar = tk.Menu(self)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open ROM...", command=self.open_rom, accelerator="Ctrl+O")
        file_menu.add_command(label="Save", command=self.save_rom, accelerator="Ctrl+S")
        file_menu.add_command(label="Save As...", command=self.save_rom_as)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_close)
        menubar.add_cascade(label="File", menu=file_menu)

        tools = tk.Menu(menubar, tearoff=0)
        tools.add_command(label="Jump to PRG start", command=lambda: self.jump_hex(self.rom.data_start if self.rom.data else 0))
        tools.add_command(label="Jump to CHR start", command=lambda: self.jump_hex(self.rom.chr_start if self.rom.data else 0))
        tools.add_command(label="Export CHR graphics blob...", command=self.export_chr)
        menubar.add_cascade(label="Tools", menu=tools)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="About", command=self.about)
        menubar.add_cascade(label="Help", menu=help_menu)
        self.config(menu=menubar)
        self.bind("<Control-o>", lambda _e: self.open_rom())
        self.bind("<Control-s>", lambda _e: self.save_rom())

    def ensure_rom(self) -> bool:
        if not self.rom.data:
            messagebox.showwarning("No ROM", "Open a legally obtained .nes ROM first.")
            return False
        return True

    def mark_dirty(self) -> None:
        self.dirty = True
        self.status.set("Modified - not saved")

    def refresh_all(self) -> None:
        self.info_tab.refresh()
        self.hex_tab.refresh()

    def maybe_save(self) -> bool:
        if not self.dirty:
            return True
        ans = messagebox.askyesnocancel("Unsaved changes", "Save changes before continuing?")
        if ans is None:
            return False
        if ans:
            return self.save_rom()
        return True

    def open_rom(self) -> None:
        if not self.maybe_save():
            return
        path = filedialog.askopenfilename(title="Open NES ROM", filetypes=[("NES ROM", "*.nes"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.rom.load(path)
            self.dirty = False
            self.status.set(f"Opened {path}")
            self.refresh_all()
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))

    def save_rom(self) -> bool:
        if not self.ensure_rom():
            return False
        if not self.rom.path:
            return self.save_rom_as()
        try:
            self.rom.save(backup=True)
            self.dirty = False
            self.status.set(f"Saved {self.rom.path} and wrote .bak backup")
            self.refresh_all()
            return True
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))
            return False

    def save_rom_as(self) -> bool:
        if not self.ensure_rom():
            return False
        path = filedialog.asksaveasfilename(title="Save ROM As", defaultextension=".nes", filetypes=[("NES ROM", "*.nes"), ("All files", "*.*")])
        if not path:
            return False
        try:
            self.rom.save(path, backup=False)
            self.dirty = False
            self.status.set(f"Saved {path}")
            self.refresh_all()
            return True
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))
            return False

    def jump_hex(self, offset: int) -> None:
        self.tabs.select(self.hex_tab)
        self.hex_tab.offset_var.set(f"0x{offset:06X}")
        self.hex_tab.refresh()

    def export_chr(self) -> None:
        if not self.ensure_rom() or not self.rom.header:
            return
        if self.rom.header.chr_size <= 0:
            messagebox.showinfo("CHR", "This ROM does not have CHR ROM banks.")
            return
        out = filedialog.asksaveasfilename(title="Export CHR blob", defaultextension=".chr", filetypes=[("CHR blob", "*.chr"), ("All files", "*.*")])
        if not out:
            return
        try:
            start = self.rom.chr_start
            Path(out).write_bytes(self.rom.read(start, self.rom.header.chr_size))
            messagebox.showinfo("CHR", f"Exported CHR data to:\n{out}")
        except Exception as exc:
            messagebox.showerror("CHR export failed", str(exc))

    def about(self) -> None:
        messagebox.showinfo(
            "About",
            "SMB ROMHacking Suite\n\n"
            "A Tkinter tool for inspecting and editing legally obtained NES ROMs.\n"
            "Share IPS patches, not full ROM files.",
        )

    def on_close(self) -> None:
        if self.maybe_save():
            self.destroy()


def main() -> None:
    app = SMBEditorApp()
    app.mainloop()


if __name__ == "__main__":
    main()
