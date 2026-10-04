#!/bin/bash
# An independent check of the proofs with nanoda, the type checker for Lean written in Rust that
# comes with the Lean toolchain, on exports written by lean4export (`leanexport`, also included).
#   part A: the closure of the main theorems, with the certificates (`C4.Cert.*.cK` and
#           `C4.Cert.*.kN_I`) as axioms;
#   part B: the closure of each certificate module, with only the three standard axioms;
#   glue:   `export_tools.py glue` matches the two parts by hashes of their declarations.
# Usage, after `lake build`:  scripts/nanoda_check.sh OUTDIR [JOBS]
# OUTDIR is written relative to the root of the project, so that the output names no absolute path.
# Part A needs up to about 7 GB of memory (for the export).  Part B checks JOBS modules at a time
# (default 8), each with under 2 GB (16 at a time needed 16 GB).  The glue needs about 6 GB.
C4DIR="$(dirname "$0")/.."
T=scripts/export_tools.py
if [ "$1" = --module ]; then  # part B for the module $3: export, configure, check
  cd "$C4DIR"
  B=$2/B/$3
  lake env leanexport C4Cert.$3 -- C4.Cert.$3.cover > $B.json &&
    python3 -B $T config $B.json $B.cfg.json &&
    lake env nanoda_bin $B.cfg.json > $B.log 2>&1 && echo "$3 ok" || echo "$3 FAILED"
  exit 0
fi
[ -n "$1" ] || { echo "usage: $0 OUTDIR [JOBS]"; exit 2; }
OUT=$(realpath -m --relative-to="$C4DIR" "$1")
cd "$C4DIR"
JOBS=${2:-8}
mkdir -p $OUT/B
ok=1
echo "part A: export the closure of the main theorems and check it"
lake env leanexport C4 -- C4.theoremA C4.theoremA_cyclic C4.theoremA_slice C4.theoremB \
  C4.albouy_square C4.prZ_isProperMap C4.not_collinear_limit C4.nondegenerate \
  C4.nondegenerate_slice C4.theoremA_analytic_slice C4.theoremA_two C4.theoremA_analytic \
  C4.ccr_injective C4.ccr_mass_injective C4.convex_count C4.convex_count_OP \
  C4.corollaryD_a C4.corollaryD_b C4.corollaryD_c C4.nocollinear C4.palmore \
  C4.area_sum_eq_zero C4.area_moment_eq_zero C4.area_simc C4.area_mirror C4.area_eq_zero_of_eq \
  C4.area_eq_zero_iff_collinear C4.quad_area C4.order1234_iff C4.order1234_ccw \
  C4.isConvex_iff_order C4.isConvex_iff_not_interior C4.concave_interior C4.dr_eq_zero_iff \
  C4.hessK_eq_zero_iff C4.selfStress_iff C4.dziobek C4.convex_signs \
  C4.convex_diagonal_longer C4.dziobek_products C4.longest_side_opposite \
  C4.hessQ_identity_abs C4.hessian_q C4.hessian_rigid C4.shape_decomp C4.shape_tangent \
  C4.shape_hessian C4.shape_index C4.shape_nondegenerate_iff C4.shape_localMin_iff \
  C4.convex_shape_min C4.palmore_shape C4.corollaryC_i C4.Shape.critical_iff \
  C4.Shape.contMDiffOn_fS C4.Shape.contMDiffAt_proj C4.eta_props C4.qd_similarOP_eq \
  C4.dziobekFn_w C4.dziobekFn_F C4.masses_unique C4.cc_iff_P C4.normal_cc C4.normal_exists \
  C4.normal_injective C4.massMap_spec C4.corollaryC_ii C4.normalize_sim C4.cc_masses \
  C4.hessian_Phi C4.ShapeHessAux.hessian_fUI_display > $OUT/main.json 2> $OUT/main.err || exit 1
# leanexport reports a missing name with a PANIC and still exits with 0
if grep -q PANIC $OUT/main.err; then cat $OUT/main.err; echo "part A FAILED"; exit 1; fi
python3 -B $T partA $OUT/main.json $OUT/mainA.json $OUT/certnames.txt || exit 1
python3 -B $T config $OUT/mainA.json $OUT/mainA.cfg.json $OUT/certnames.txt
lake env nanoda_bin $OUT/mainA.cfg.json > $OUT/mainA.log 2>&1 &&
  tail -n 1 $OUT/mainA.log && echo "part A ok" || { echo "part A FAILED"; ok=0; }
echo "part B: export and check the certificate modules, $JOBS at a time"
ls C4Cert | sed -n 's/^\(Dir[0-9]*\|Ch[0-9]*\)\.lean$/\1/p' |
  xargs -P $JOBS -I{} scripts/nanoda_check.sh --module $OUT {} > $OUT/B.log
echo "part B: $(grep -c ' ok$' $OUT/B.log) modules ok, $(grep -c FAILED $OUT/B.log) failed"
grep -q FAILED $OUT/B.log && ok=0
echo "glue"
python3 -B $T glue $OUT/mainA.json $OUT/certnames.txt $OUT/B/*[0-9].json || ok=0
[ $ok = 1 ] && echo "ALL CHECKS PASSED" || { echo "SOME CHECKS FAILED"; exit 1; }
