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
#include <map>
#include <sstream>
#include <vector>
#include <cstdlib>
#include <cstring>

#include <capstone/capstone.h>

#include "main.h"
#include "vita.h"
#include "utils.h"

#include "instructions.h"

#include "import/vita-import.h"

#define INDENT "\t"
#define MAX_ARGS 8

// TODO: compose conditionals
// TODO: write evaluate functions to simplify code
// TODO: output idc
// TODO: aliases
// TODO: input data section

/*
	Ideas:
	- Save labels in a list for every subroutine
	- Labels hold information about what registers they depend on
*/

struct SymbolEntry {
	int type;
	std::string name;
	int n_args;
	int args_stats[MAX_ARGS];
};

struct RegisterAssignmentEntry {
	std::string assign;
	uint32_t addr;
	bool update_flags;
};

typedef std::map<uint32_t, SymbolEntry *> SymbolMap;

typedef std::map<uint32_t, uint32_t> MovwMap;
typedef std::map<uint32_t, bool> IgnoreMap;

typedef std::map<int, RegisterAssignmentEntry *> RegisterAssignmentMap;

static SymbolMap g_symbol_map;

static MovwMap g_movw_map;
static IgnoreMap g_ignore_map;

static RegisterAssignmentMap g_reg_assign_map;

static bool g_use_flags = false;

static std::string g_condition_reg_1;
static std::string g_condition_reg_2;

static csh handle;

static uint32_t g_text_addr = 0, g_text_size = 0, g_mod_info_offset = 0;

int ReadFile(const char *file, uint8_t *buf, size_t size)
{
	FILE *f = fopen(file, "rb");

	if (!f)
		return -1;

	int rd = fread(buf, 1, size, f);
	fclose(f);

	return rd;
}

static bool isConditional(cs_arm *arm) {
	if (arm == NULL)
		return false;

	return arm->cc != ARM_CC_AL && arm->cc != ARM_CC_INVALID;
}

static void freeRegAssignMap() {
	for (auto it = g_reg_assign_map.begin(); it != g_reg_assign_map.end(); it++) {
		delete it->second;
	}

	g_reg_assign_map.clear();
}

static void clearRegAssignMapAfterBranch() {
	delete g_reg_assign_map[ARM_REG_R0];
	delete g_reg_assign_map[ARM_REG_R1];
	delete g_reg_assign_map[ARM_REG_R2];
	delete g_reg_assign_map[ARM_REG_R3];

	g_reg_assign_map[ARM_REG_R0] = NULL;
	g_reg_assign_map[ARM_REG_R1] = NULL;
	g_reg_assign_map[ARM_REG_R2] = NULL;
	g_reg_assign_map[ARM_REG_R3] = NULL;
}

static std::string getImmString(uint32_t imm, bool is_mem)
{
	char buf[64];

	if (((int)imm >= -9 && (int)imm < 0) || ((int)imm >= 0 && (int)imm <= 9) ||
		(is_mem && (imm & 0x80000000))) {
		snprintf(buf, sizeof(buf), "%d", imm);
	} else {
		snprintf(buf, sizeof(buf), "0x%X", imm);
	}

	return buf;
}

static std::string getInstructionCode(cs_arm *arm, const std::string& mnemonic)
{
	// Is known instruction?
	if (instructions.count(mnemonic) == 0)
		return "";

	std::string code(instructions[mnemonic]);

	// Instructions with 2 op's only
	if (arm->op_count == 2) {
		if (instructions2.count(mnemonic) > 0) {
			code = instructions2[mnemonic];
		}
	}

	// Update flags
	if (arm->update_flags) {
		if (mnemonic.compare("cmp") != 0 &&
			mnemonic.compare("cmn") != 0 &&
			mnemonic.compare("tst") != 0) {
			code += "\\FLAGS = op0;";
		}
	}

	return code;
}

static std::string trimMnemonic(cs_arm *arm, std::string mnemonic, std::string* cond_flags, std::string *cond_regs)
{
	// Remove '.w' suffix
	mnemonic = mnemonic.substr(0, mnemonic.find(".w"));

	// Remove condition suffix
	if (isConditional(arm)) {
		std::string cond = mnemonic.substr(mnemonic.size()-2, 2);
	    if (conditions.count(cond) > 0) {
			if (cond_flags != NULL)
				*cond_flags = conditions[cond].cond_flags;
			
			if (cond_regs != NULL)
				*cond_regs = conditions[cond].cond_regs;
			
			mnemonic = mnemonic.substr(0, mnemonic.size()-2);
		}
	}

	// Remove 's' suffix
	if (arm->update_flags) {
		if (mnemonic[mnemonic.size()-1] == 's')
			mnemonic = mnemonic.substr(0, mnemonic.size()-1);
	}

	return mnemonic;
}

static void ignoreAddr(int reg) {
/*	// Do not ignore other registers than r0-r3
	if (!(reg >= ARM_REG_R0 && reg < ARM_REG_R4))
		return;
*/
	if (g_reg_assign_map[reg] != NULL) {
		if (g_reg_assign_map[reg]->update_flags && g_use_flags)
			return;

		g_ignore_map[g_reg_assign_map[reg]->addr] = true;
	}
}

static std::string getArgsString(int n_args, bool input, bool analyse)
{
	std::stringstream output;

	for (int i = 0; i < ((n_args < MAX_ARGS) ? n_args : MAX_ARGS); i++) {
		if (input) {
			if (i < 4) {
				if (g_reg_assign_map[ARM_REG_R0+i] != NULL) {
					output << g_reg_assign_map[ARM_REG_R0+i]->assign << ", ";
					
					if (analyse)
						ignoreAddr(ARM_REG_R0+i);
				} else {
					output << "a" << (i+1) << ", ";
				}
			} else {
				output << "*(sp+" << ((i-4)*4) << "), ";
			}
		} else {
			output << "int arg" << (i+1) << ", ";
		}
	}

	std::string out_str = output.str();
	return out_str.substr(0, out_str.size()-2);
}

static void handleShift(std::string& reg, cs_arm_op *op)
{
	if (op->shift.type != ARM_SFT_INVALID && op->shift.value) {
		std::string shift_op = shifts[op->shift.type];

		char buf[256];

		if (op->shift.type < ARM_SFT_ASR_REG) {
			snprintf(buf, sizeof(buf), "(%s %s 0x%X)", reg.c_str(), shift_op.c_str(), op->shift.value);
		} else {
			snprintf(buf, sizeof(buf), "(%s %s %s)", reg.c_str(), shift_op.c_str(), getRegName(handle, op->shift.value).c_str());
		}

		reg = buf;
	}
}

static void assignRegister(cs_insn *insn, const std::string& mnemonic, uint32_t addr, std::string& code, bool analyse) {
	cs_arm *arm = &(insn->detail->arm);

	cs_arm_op *op0 = &(arm->operands[0]);

	// Is conditional instruction
	if (isConditional(arm)) {
		// Do not compose it
		delete g_reg_assign_map[op0->mem.base];
		g_reg_assign_map[op0->mem.base] = NULL;
	} else {
		std::string assign = code.substr(5, code.find(";")-5);
		
		if (mnemonic.compare("movt") == 0) {
			if (g_reg_assign_map[op0->mem.base] != NULL) {
				if (isHex(g_reg_assign_map[op0->mem.base]->assign) ||
					isDec(g_reg_assign_map[op0->mem.base]->assign)) {
					uint32_t movt_val = strToHex(assign.substr(0, assign.find(" ")));
					uint32_t movw_val = strToHex(g_reg_assign_map[op0->mem.base]->assign);
					
					uint32_t value = movt_val | movw_val;
					
					char buf[256];
					snprintf(buf, sizeof(buf), "0x%08X", value);

					if (value >= g_text_addr && value < g_text_addr+g_text_size) {
						if (value < g_text_addr+g_mod_info_offset) {
							value &= ~0x1;
							
							if (g_symbol_map[value] != NULL && g_symbol_map[value]->type & SYMBOL_SUBROUTINE) {
								snprintf(buf, sizeof(buf), (g_symbol_map[value]->name).c_str());
							} else {
								snprintf(buf, sizeof(buf), "g_text_%08X", value);
							}
						} else {
							if (g_symbol_map[value] != NULL && g_symbol_map[value]->type & SYMBOL_STRING) {
								snprintf(buf, sizeof(buf), "\"%s\"", (g_symbol_map[value]->name).c_str());
							} else {
								snprintf(buf, sizeof(buf), "g_text_%08X", value);
							}
						}
					}
					
					code = getRegName(handle, op0->mem.base) + " = " + buf + ";";
					assign = buf;
					
					if (analyse)
						ignoreAddr(op0->mem.base);
				}
			}
		}
		
		// Register assignment
		if (g_reg_assign_map[op0->mem.base] == NULL)
			g_reg_assign_map[op0->mem.base] = new RegisterAssignmentEntry();
		
		RegisterAssignmentEntry *entry = g_reg_assign_map[op0->mem.base];
		entry->assign = assign;
		entry->addr = addr;
		entry->update_flags = arm->update_flags;
	}
}

static void composeRegister(std::string& reg_str, int reg, bool analyse)
{
	// Do not compose sp reg
	if (reg == ARM_REG_R13)
		return;

	// Register is in memory, can be composed
	if (g_reg_assign_map[reg] != NULL && g_reg_assign_map[reg]->assign.size() < 128) {
		std::string assign(g_reg_assign_map[reg]->assign);
		
		bool is_string = isString(assign);
		bool is_atom = assign.find(" ") == std::string::npos;

		bool set_brackets = !is_string && !is_atom;
		
		// Open brackets if needed
		if (set_brackets)
			reg_str = "(";
		else
			reg_str = "";
		
		// Composing
		reg_str += assign;
		
		// Close brackets if needed
		if (set_brackets)
			reg_str += ")";
		
		if (analyse)
			ignoreAddr(reg);
	}
}

static void parseOperations(cs_insn *insn, const std::string& mnemonic, uint32_t addr, std::string& code, bool analyse) {
	cs_arm *arm = &(insn->detail->arm);

	bool is_cmp = mnemonic.compare("cmp") == 0;

	for (int i = 0; i < arm->op_count; i++) {
		std::stringstream op_name;
		op_name << "op" << i;

		cs_arm_op *op = &(arm->operands[i]);
		switch((int)op->type) {
			case ARM_OP_REG:
			{
				std::string reg = getRegName(handle, op->mem.base);
				
				// Composing
				if (code.find(op_name.str() + " = ") == std::string::npos) {
					composeRegister(reg, op->mem.base, analyse);
				}
				
				// Handle shift
				if (i == arm->op_count-1) {
					handleShift(reg, op);
				}
				
				// Is comparison. TODO
				if (is_cmp) {
					if (i == 0) {
						g_condition_reg_1 = reg;
					} else if (i == 1) {
						g_condition_reg_2 = reg;
					}
					/*
					if (analyse)
						g_ignore_map[addr] = true;
					*/
				}
				
				// Replace operand
				replaceAll(code, op_name.str(), reg);
				
				break;
			}
			
			case ARM_OP_IMM:
			{
				// Replace operand
				replaceAll(code, op_name.str(), getImmString(op->imm, false));
				break;
			}
			
			case ARM_OP_MEM:
			{
				std::string str;
				std::string reg = getRegName(handle, op->mem.base);
				
				// Composing
				if (code.find(op_name.str() + " = ") == std::string::npos) {
					composeRegister(reg, op->mem.base, analyse);
				}
				
				if (op->mem.index != ARM_REG_INVALID) {
					std::string reg2 = getRegName(handle, op->mem.index);
					handleShift(reg2, &(arm->operands[0]));
					str = reg + " + " + reg2;
				} else {
					str = reg + " + " + getImmString(op->mem.disp, true);
				}
				
				// Simplify. TODO: replace this by evaluator
				size_t pos = str.find(" + 0", str.size()-4);
				if (pos != std::string::npos)
					str = str.substr(0, pos);
				
				// Replace operand
				replaceAll(code, op_name.str(), str);
				
				break;
			}
		}
	}
}

static void translateCode(cs_insn *insn, const std::string& mnemonic, uint32_t addr, std::string& code, bool analyse)
{
	cs_arm *arm = &(insn->detail->arm);

	// A conditional is dependant on the flags
	if (isConditional(arm))
		g_use_flags = true;

	// It has been updated, set to false
	if (arm->update_flags) {
		g_use_flags = false;
		
		// Reset condition regs too
		g_condition_reg_1 = "";
		g_condition_reg_2 = "";
	}

	// Parse operations
	parseOperations(insn, mnemonic, addr, code, analyse);

	// Register assignment
	if (code[3] == '=' && code.compare(5, 6, "symbol") != 0) {
		assignRegister(insn, mnemonic, addr, code, analyse);
	}
	
	// Replace symbol
	for (int i = 0; i < 2; i++) {
		cs_arm_op *op = &(arm->operands[i]);
		if (g_symbol_map[op->imm] != NULL) {
			if (g_symbol_map[op->imm]->type & (SYMBOL_SUBROUTINE | SYMBOL_LABEL)) {
				replaceAll(code, "symbol", g_symbol_map[op->imm]->name);
				
				if (g_symbol_map[op->imm]->type & SYMBOL_SUBROUTINE)
					replaceAll(code, "...", getArgsString(g_symbol_map[op->imm]->n_args, true, analyse));
			}
		} else {
			if (i == 1)
				replaceAll(code, "symbol", insn->op_str);
		}
	}
	
	// Clear args map after branch
	if (mnemonic.compare("bl") == 0 || mnemonic.compare("blx") == 0) {
		clearRegAssignMapAfterBranch();
		
		// Flags are no longer up-to-date, set to false
		g_use_flags = false;
	}
}

static void pseudoCode(cs_insn *insn, uint32_t addr)
{
	std::string indent = INDENT;
	std::string cond_flags = "";
	std::string cond_regs = "";

	cs_arm *arm = &(insn->detail->arm);

	std::string mnemonic = trimMnemonic(arm, insn->mnemonic, &cond_flags, &cond_regs);

	// Get instruction code
	std::string code = getInstructionCode(arm, mnemonic);
	if (code.empty()) {
		std::string op_str(insn->op_str);
		if (mnemonic.compare("bx") == 0 && op_str.compare("lr") == 0)
			std::cout << indent << "return a1;" << std::endl;
		else if (mnemonic.compare("pop") == 0)
			std::cout << indent << "return a1; // " << mnemonic << " " << insn->op_str << std::endl;
		else if (mnemonic.compare("push") == 0)
			std::cout << indent << "// " << mnemonic << " " << insn->op_str << std::endl;
		else if (mnemonic.compare("nop") == 0 || mnemonic.compare(0, 2, "it") == 0)
			std::cout << ""; // Nothing
		else
			std::cout << indent << "asm(\"" << mnemonic << " " << insn->op_str << "\\n\");" << std::endl;
		
		return;
	}

	// Translate code
	translateCode(insn, mnemonic, addr, code, false);

	// Condition
	if (cond_flags != "" || cond_regs != "") {
		// TODO: compose conditions
		/*if (g_condition_reg_1 != "" && g_condition_reg_2 != "") {
			replaceAll(cond_regs, "COND_X", g_condition_reg_1);
			replaceAll(cond_regs, "COND_Y", g_condition_reg_2);

			std::cout << indent << cond_regs << "" << std::endl;
		} else {*/
			std::cout << indent << cond_flags << "" << std::endl;
		//}
		
		indent += "\t";
	}

	// Replace '\' with newline
	replaceAll(code, "\\", "\n" + indent);

	if (g_ignore_map[addr]) return;

	// Output
	std::cout << indent;

	if (g_ignore_map[addr]) {
		std::cout << "// ";
		replaceAll(code, INDENT, INDENT "// ");
	}

	std::cout << code << std::endl;
}

static int decompile(uint8_t *data)
{
	cs_err err = cs_open(CS_ARCH_ARM, CS_MODE_THUMB, &handle);
	if (err) {
		return -1;
	}

	cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);

	cs_insn *insn = cs_malloc(handle);

	bool first_import = true, first = true;

	const uint8_t *code = data;
	uint32_t size = g_mod_info_offset;
	uint32_t address = g_text_addr;

	while (size > 0) {
		// Reset at new subroutine/label
		if (g_symbol_map[address] != NULL) {
			freeRegAssignMap();
			g_use_flags = false;
		}

		// Import
		if (g_symbol_map[address] != NULL) {
			if (g_symbol_map[address]->type & SYMBOL_IMPORT) {
				if (first_import) {
					std::cout << "}\n\n";
					first_import = false;
				}
				
				std::cout << "int " << g_symbol_map[address]->name << "(" << getArgsString(g_symbol_map[address]->n_args, false, false) << ");" << std::endl;
				
				address += 0x10;
				code += 0x10;
				size -= 0x10;
				continue;
			}
		}

		// Subroutine/label start
		if (g_symbol_map[address] != NULL) {
			if (g_symbol_map[address]->type & SYMBOL_SUBROUTINE) {
				if (first) {
					first = false;
				} else {
					std::cout << "}\n\n";
				}

				if (g_symbol_map[address]->type & SYMBOL_IMPORT) {
					printf("// Imported 0x%08X\n", address);
				} else if (g_symbol_map[address]->type & SYMBOL_EXPORT) {
					printf("// Exported 0x%08X\n", address);
				}

				std::cout << "int " << g_symbol_map[address]->name << "(" << getArgsString(g_symbol_map[address]->n_args, false, false) << ")" << std::endl << "{" << std::endl;
			} else if (g_symbol_map[address]->type & SYMBOL_LABEL) {
				std::cout << std::endl << g_symbol_map[address]->name << ":" << std::endl;
			}
		}

		// Disassemble
		uint32_t addr = address;

		int res = cs_disasm_iter(handle, &code, (size_t *)&size, (uint64_t *)&address, insn);
		if (res == 0) {
			uint32_t opcode;
			memcpy(&opcode, code + address-g_text_addr, sizeof(uint32_t));
			printf("\tasm(\".word 0x%08X\\n\");\n", opcode);

			address += 2;
			code += 2;
			size -= 2;

			continue;
		}

		// Output pseudo code
		pseudoCode(insn, addr);
	}

	cs_free(insn, 1);

	cs_close(&handle);

	return 0;
}

static int analyseCode(uint8_t *data) {
	cs_err err = cs_open(CS_ARCH_ARM, CS_MODE_THUMB, &handle);
	if (err) {
		return -1;
	}

	cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);

	cs_insn *insn = cs_malloc(handle);

	const uint8_t *code = data;
	uint32_t size = g_mod_info_offset;
	uint32_t address = g_text_addr;

	while (size > 0) {
		// Reset at new subroutine/label
		if (g_symbol_map[address] != NULL) {
			freeRegAssignMap();
			g_use_flags = false;
		}

		// Disassemble
		uint32_t addr = address;

		int res = cs_disasm_iter(handle, &code, (size_t *)&size, (uint64_t *)&address, insn);
		if (res == 0) {
			address += 2;
			code += 2;
			size -= 2;
			continue;
		}

		cs_arm *arm = &(insn->detail->arm);

		std::string mnemonic = trimMnemonic(arm, insn->mnemonic, NULL, NULL);

		// Get instruction code
		std::string code = getInstructionCode(arm, mnemonic);
		if (code.empty())
			continue;

		// Translate code
		translateCode(insn, mnemonic, addr, code, true);
	}

	cs_free(insn, 1);

	cs_close(&handle);

	return 0;
}

static int analyseArguments(uint8_t *data) {
	int n_args = 0;

	cs_err err = cs_open(CS_ARCH_ARM, CS_MODE_THUMB, &handle);
	if (err) {
		return -1;
	}

	cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);

	cs_insn *insn = cs_malloc(handle);

	const uint8_t *code = data;
	uint32_t size = g_mod_info_offset;
	uint32_t address = g_text_addr;

	while (size > 0) {
		// Disassemble
		uint32_t addr = address;

		int res = cs_disasm_iter(handle, &code, (size_t *)&size, (uint64_t *)&address, insn);
		if (res == 0) {
			address += 2;
			code += 2;
			size -= 2;
			continue;
		}

		// Reset at new subroutine/label
		if (g_symbol_map[addr] != NULL) {
			n_args = 0;
		}

		cs_arm *arm = &(insn->detail->arm);

		std::string mnemonic = trimMnemonic(arm, insn->mnemonic, NULL, NULL);

		// Get instruction code
		std::string code = getInstructionCode(arm, mnemonic);
		if (code.empty())
			continue;

		if (mnemonic.compare("str") == 0) {
			cs_arm_op *op = &(arm->operands[1]);

			if (op->mem.base == ARM_REG_R13) {
				if (op->mem.disp >= 0 && op->mem.disp < 0xC) {
					int n_stack_args = (op->mem.disp >> 2) + 1;
					if (n_args <= 4+n_stack_args)
						n_args = 4+n_stack_args;
				}
			}
		} else if (mnemonic.compare("strd") == 0) {
			cs_arm_op *op = &(arm->operands[2]);

			if (op->mem.base == ARM_REG_R13) {
				if (op->mem.disp >= 0 && op->mem.disp < 0xC) {
					int n_stack_args = (op->mem.disp >> 2) + 1;
					if (n_args <= 4+n_stack_args)
						n_args = 4+n_stack_args;
				}
			}
		} else {
			if (code.find("op0 = ") != std::string::npos) {
				cs_arm_op *op = &(arm->operands[0]);
				
				if (op->mem.base >= ARM_REG_R0 && op->mem.base < ARM_REG_R4) {
					if (op->mem.base == ARM_REG_R0 && n_args <= 0)
						n_args = 1;
					else if (op->mem.base == ARM_REG_R1 && n_args <= 1)
						n_args = 2;
					else if (op->mem.base == ARM_REG_R2 && n_args <= 2)
						n_args = 3;
					else if (op->mem.base == ARM_REG_R3 && n_args <= 3)
						n_args = 4;
				}
				
				if (mnemonic.compare("ldrd") == 0) {
					cs_arm_op *op = &(arm->operands[1]);
					
					if (op->mem.base >= ARM_REG_R0 && op->mem.base < ARM_REG_R4) {
						if (op->mem.base == ARM_REG_R0 && n_args <= 0)
							n_args = 1;
						else if (op->mem.base == ARM_REG_R1 && n_args <= 1)
							n_args = 2;
						else if (op->mem.base == ARM_REG_R2 && n_args <= 2)
							n_args = 3;
						else if (op->mem.base == ARM_REG_R3 && n_args <= 3)
							n_args = 4;
					}
				}
			}
		}

		// Function call
		if (mnemonic.compare("bl") == 0 || mnemonic.compare("blx") == 0) {
			cs_arm_op *op = &(arm->operands[0]);

			if ((uint32_t)op->imm >= g_text_addr && (uint32_t)op->imm < (g_text_addr+g_text_size)) {
				if (g_symbol_map[op->imm]) {					
					if (n_args < MAX_ARGS)
						g_symbol_map[op->imm]->args_stats[n_args]++;
				}
			}

			n_args = 0;
		}
	}

	for (auto it = g_symbol_map.begin(); it != g_symbol_map.end(); it++) {
		SymbolEntry *entry = it->second;
		
		if (entry != NULL && entry->type & SYMBOL_SUBROUTINE) {
			int reg = 0, max = 0;
			
			for (int i = 0; i < MAX_ARGS; i++) {
				if (entry->args_stats[i] > max) { // TODO: or >=
					max = entry->args_stats[i];
					reg = i;
				}
			}
			
			entry->n_args = reg;
		}
	}

	cs_free(insn, 1);

	cs_close(&handle);

	return 0;
}

void addSymbol(uint32_t addr, std::string name, int type)
{
	if (g_symbol_map[addr] == NULL) {
		SymbolEntry *s = new SymbolEntry();
		s->type = type;
		s->name = name;
		g_symbol_map[addr] = s;
	}	
}

static int analyseSymbols(uint8_t *data, bool secondRun)
{
	cs_err err = cs_open(CS_ARCH_ARM, CS_MODE_THUMB, &handle);
	if (err) {
		return -1;
	}

	cs_option(handle, CS_OPT_DETAIL, CS_OPT_ON);

	cs_insn *insn = cs_malloc(handle);

	const uint8_t *code = data;
	uint32_t size = g_mod_info_offset;
	uint32_t address = g_text_addr;

	while (size > 0) {
		// Disassemble
		int res = cs_disasm_iter(handle, &code, (size_t *)&size, (uint64_t *)&address, insn);
		if (res == 0) {
			address += 2;
			code += 2;
			size -= 2;
			continue;
		}

		cs_arm *arm = &(insn->detail->arm);

		std::string mnemonic = trimMnemonic(arm, insn->mnemonic, NULL, NULL);

		if (!secondRun) {
			bool isBranch = mnemonic.compare("b") == 0;
			if (isBranch || mnemonic.compare("bl") == 0 || mnemonic.compare("blx") == 0) {
				cs_arm_op *op = &(arm->operands[0]);

				if ((uint32_t)op->imm >= g_text_addr && (uint32_t)op->imm < (g_text_addr+g_text_size)) {
					if (g_symbol_map[op->imm] == NULL) {
						char name[64];
						snprintf(name, sizeof(name), "%s_%08X", isBranch ? "loc" : "sub", op->imm);
						addSymbol(op->imm, name, isBranch ? SYMBOL_LABEL : SYMBOL_SUBROUTINE);
					}
				}
			}
			
			if (mnemonic.compare("cbz") == 0 || mnemonic.compare("cbnz") == 0) {
				cs_arm_op *op = &(arm->operands[1]);

				if ((uint32_t)op->imm >= g_text_addr && (uint32_t)op->imm < (g_text_addr+g_text_size)) {
					if (g_symbol_map[op->imm] == NULL) {
						char name[64];
						snprintf(name, sizeof(name), "loc_%08X", op->imm);
						addSymbol(op->imm, name, SYMBOL_LABEL);
					}
				}
			}
			
			if (mnemonic.compare("mov") == 0 || mnemonic.compare("movw") == 0) {
				cs_arm_op *op0 = &(arm->operands[0]);
				cs_arm_op *op1 = &(arm->operands[1]);
				g_movw_map[op0->mem.base] = op1->imm;
			}

			if (mnemonic.compare("movt") == 0) {
				cs_arm_op *op0 = &(arm->operands[0]);
				cs_arm_op *op1 = &(arm->operands[1]);
				uint32_t value = (op1->imm << 16) | g_movw_map[op0->mem.base];

				if (value >= g_text_addr && value < g_text_addr+g_text_size) {
					if (value < g_text_addr+g_mod_info_offset) {
						char name[64];
						snprintf(name, sizeof(name), "sub_%08X", value & ~0x1);
						addSymbol(value & ~0x1, name, SYMBOL_SUBROUTINE);
					} else {						
						// Is ascii string with minimum length of 4
						char *string = (char *)(data + (value-g_text_addr));
						
						int i = 0;
						while (string[i] >= 0x20 && (value-g_text_addr+i) < g_text_size) {
							i++;
						}
						
						if (i >= 4) {
							std::string string_data(string);
							replaceAll(string_data, "\n", "");
							addSymbol(value, string_data, SYMBOL_STRING);
						}
					}
				}
			}
		} else {
			const uint8_t *code2 = code;
			uint32_t size2 = size;
			uint32_t address2 = address;
			cs_disasm_iter(handle, &code2, (size_t *)&size2, (uint64_t *)&address2, insn);

			std::string mnemonic2(insn->mnemonic);

			if (mnemonic.compare("pop") == 0 || mnemonic.compare("bx") == 0) {
				uint32_t addr = address;
				if (mnemonic2.compare("nop") == 0)
					addr = address2;
				if (g_symbol_map[addr] == NULL) {
					char name[64];
					snprintf(name, sizeof(name), "sub_%08X", addr);
					addSymbol(addr, name, SYMBOL_SUBROUTINE);
				}
			}
		}
	}

	if (secondRun) {
		// Subroutine at text_addr+0 doesn't exist yet
		if (g_symbol_map[g_text_addr] == NULL) {
			char name[64];
			snprintf(name, sizeof(name), "sub_%08X", g_text_addr);
			addSymbol(g_text_addr, name, SYMBOL_SUBROUTINE);
		}
	}

	cs_free(insn, 1);

	cs_close(&handle);

	return 0;
}

static vita_imports_t *imports;

char *findNameByNid(const char *libname, uint32_t nid)
{
	for (int i = 0; i < imports->n_libs; i++) {
		vita_imports_lib_t *lib_entry = imports->libs[i];
		if (lib_entry == NULL)
			continue;

		for (int i = 0; i < lib_entry->n_modules; i++) {
			vita_imports_module_t *module_entry = lib_entry->modules[i];
			
			if (module_entry && strcmp(module_entry->name, libname) == 0) {
				for (int i = 0; i < module_entry->n_functions; i++) {
					vita_imports_stub_t *stub_entry = module_entry->functions[i];
					
					if (stub_entry && stub_entry->NID == nid)
						return stub_entry->name;
				}

				return NULL;
			}
		}
	}

	return NULL;
}

static void usage(char *argv[])
{
	std::cout << argv[0] << " " << "binary" << " " << "address" << " " << "yml";
}

// Example: vitadecompiler SceIdStorage_text_0x018B4000.bin 0x018B4000 db.yml > SceIdStorage.c

int main(int argc, char *argv[])
{
	if (argc < 4) {
		usage(argv);
		return 1;
	}

	imports = vita_imports_load(argv[3], 0);

	uint8_t *data = (uint8_t *)malloc(16 * 1024 * 1024);
	if (!data) {
		std::cerr << "Error could not allocate memory." << std::endl;
		return 1;
	}

	int res = ReadFile(argv[1], data, 16 * 1024 * 1024);
	g_text_size = res;
	if (res < 0) {
		std::cerr << "Error could not read data." << std::endl;
		return 1;
	}

	g_text_addr = strtoul(argv[2], NULL, 0x10);

	g_mod_info_offset = analyseVitaModule(data, g_text_addr, g_text_size);
	if (g_mod_info_offset == 0) {
		std::cerr << "Error could not find module info." << std::endl;
		g_mod_info_offset = g_text_size;
	}

	std::cerr << "Analysing symbols..." << std::endl;
	analyseSymbols(data, false);
	analyseSymbols(data, true);

	std::cerr << "Analysing arguments..." << std::endl;
	analyseArguments(data);

	std::cerr << "Analysing code..." << std::endl;
	analyseCode(data);

	std::cerr << "Decompiling..." << std::endl;
	decompile(data);

	std::cerr << "Finished." << std::endl;

	free(data);

	return 0;
}
