/*
	VitaDecompiler
	Copyright (C) 2017, TheFloW

	This program is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <cstdlib>
#include <cstring>

#include "main.h"
#include "vita.h"

struct SyslibEntry {
	uint32_t nid;
	const char *name;
};

static SyslibEntry syslib_nids[] = {
	{ 0x70FBA1E7, "module_process_param" },
	{ 0x6C2224BA, "module_info" },
	{ 0x935CD196, "module_start" },
	{ 0x79F8E492, "module_stop" },
	{ 0x913482A9, "module_exit" },
};

static void convertToImportsTable3xx(SceImportsTable2xx *import_2xx, SceImportsTable3xx *import_3xx)
{
	memset(import_3xx, 0, sizeof(SceImportsTable3xx));

	if (import_2xx->size == sizeof(SceImportsTable2xx)) {
		import_3xx->size = import_2xx->size;
		import_3xx->lib_version = import_2xx->lib_version;
		import_3xx->attribute = import_2xx->attribute;
		import_3xx->num_functions = import_2xx->num_functions;
		import_3xx->num_vars = import_2xx->num_vars;
		import_3xx->module_nid = import_2xx->module_nid;
		import_3xx->lib_name = import_2xx->lib_name;
		import_3xx->func_nid_table = import_2xx->func_nid_table;
		import_3xx->func_entry_table = import_2xx->func_entry_table;
		import_3xx->var_nid_table = import_2xx->var_nid_table;
		import_3xx->var_entry_table = import_2xx->var_entry_table;
	} else if (import_2xx->size == sizeof(SceImportsTable3xx)) {
		memcpy(import_3xx, import_2xx, sizeof(SceImportsTable3xx));
	}
}

uint32_t analyseVitaModule(uint8_t *data, uint32_t text_addr, uint32_t text_size)
{
	uint32_t mod_info_offset = 0;

	uint32_t addr = 0;
	while (addr < text_size - 0x10) {
		if (*(uint32_t *)(data + addr) == 0x01010000 ||
			*(uint32_t *)(data + addr) == 0x01010007) {
			mod_info_offset = addr;
			break;
		}

		addr += 4;
	}

	if (mod_info_offset == 0)
		return 0;

	SceModuleInfo *mod_info = (SceModuleInfo *)(data + mod_info_offset);

	std::cerr << "Module name: " << mod_info->name << std::endl;

	uint32_t i = 0;

	i = mod_info->expTop;
	while (i < mod_info->expBtm) {
		SceExportsTable *exp = (SceExportsTable *)(data + i);

		char *lib_name = (char *)((uintptr_t)data + (exp->lib_name - text_addr));
		uintptr_t *nid_table = (uintptr_t *)((uintptr_t)data + (exp->nid_table - text_addr));
		uintptr_t *entry_table = (uintptr_t *)((uintptr_t)data + (exp->entry_table - text_addr));

		int j;
		for (j = 0; j < exp->num_functions; j++) {
			uint32_t nid = nid_table[j];
			uint32_t addr = entry_table[j];

			char name[64];

			if (exp->lib_name) {
				char *funcName = findNameByNid(lib_name, nid);
				if (funcName)
					snprintf(name, sizeof(name), funcName);
				else
					snprintf(name, sizeof(name), "%s_%08X", lib_name, nid);
			} else {
				for (uint32_t i = 0; i < (sizeof(syslib_nids) / sizeof(SyslibEntry)); i++) {
					if (syslib_nids[i].nid == nid)
						snprintf(name, sizeof(name), "%s", syslib_nids[i].name);
				}
			}

			addSymbol(addr & ~0x1, name, SYMBOL_SUBROUTINE | SYMBOL_EXPORT);
		}

		i += exp->size;
	}

	i = mod_info->impTop;
	while (i < mod_info->impBtm) {
		SceImportsTable3xx imp;
		convertToImportsTable3xx((SceImportsTable2xx *)(data + i), &imp);

		if (imp.lib_name) {
			char *lib_name = (char *)((uintptr_t)data + (imp.lib_name - text_addr));
			uintptr_t *nid_table = (uintptr_t *)((uintptr_t)data + (imp.func_nid_table - text_addr));
			uintptr_t *entry_table = (uintptr_t *)((uintptr_t)data + (imp.func_entry_table - text_addr));

			int j;
			for (j = 0; j < imp.num_functions; j++) {
				uint32_t nid = nid_table[j];
				uint32_t addr = entry_table[j];
				
				char name[64];
				
				char *funcName = findNameByNid(lib_name, nid);
				if (funcName)
					snprintf(name, sizeof(name), funcName);
				else
					snprintf(name, sizeof(name), "%s_%08X", lib_name, nid);
				
				addSymbol(addr, name, SYMBOL_SUBROUTINE | SYMBOL_IMPORT);
			}
		}

		i += imp.size;
	}

	return mod_info_offset;
}