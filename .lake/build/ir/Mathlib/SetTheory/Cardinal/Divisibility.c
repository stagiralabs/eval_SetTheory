// Lean compiler output
// Module: Mathlib.SetTheory.Cardinal.Divisibility
// Imports: Init VerifiedAgora.tagger Mathlib.Algebra.IsPrimePow Mathlib.SetTheory.Cardinal.Arithmetic Mathlib.Tactic.WLOG
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Cardinal_instUniqueUnits___closed__1;
extern lean_object* l_Cardinal_orderedCommSemiring;
static lean_object* l_Cardinal_instUniqueUnits___closed__4;
LEAN_EXPORT lean_object* l_Cardinal_instUniqueUnits;
lean_object* l_Semiring_toMonoidWithZero___rarg(lean_object*);
static lean_object* l_Cardinal_instUniqueUnits___closed__3;
static lean_object* l_Cardinal_instUniqueUnits___closed__2;
static lean_object* _init_l_Cardinal_instUniqueUnits___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Cardinal_orderedCommSemiring;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Semiring_toMonoidWithZero___rarg(x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Cardinal_instUniqueUnits___closed__2() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Cardinal_instUniqueUnits___closed__3() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Cardinal_instUniqueUnits___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Cardinal_instUniqueUnits___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Cardinal_instUniqueUnits() {
_start:
{
lean_object* x_1; 
x_1 = l_Cardinal_instUniqueUnits___closed__4;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_IsPrimePow(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_SetTheory_Cardinal_Arithmetic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_WLOG(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_SetTheory_Cardinal_Divisibility(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_IsPrimePow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_SetTheory_Cardinal_Arithmetic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_WLOG(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Cardinal_instUniqueUnits___closed__1 = _init_l_Cardinal_instUniqueUnits___closed__1();
lean_mark_persistent(l_Cardinal_instUniqueUnits___closed__1);
l_Cardinal_instUniqueUnits___closed__2 = _init_l_Cardinal_instUniqueUnits___closed__2();
lean_mark_persistent(l_Cardinal_instUniqueUnits___closed__2);
l_Cardinal_instUniqueUnits___closed__3 = _init_l_Cardinal_instUniqueUnits___closed__3();
lean_mark_persistent(l_Cardinal_instUniqueUnits___closed__3);
l_Cardinal_instUniqueUnits___closed__4 = _init_l_Cardinal_instUniqueUnits___closed__4();
lean_mark_persistent(l_Cardinal_instUniqueUnits___closed__4);
l_Cardinal_instUniqueUnits = _init_l_Cardinal_instUniqueUnits();
lean_mark_persistent(l_Cardinal_instUniqueUnits);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
