module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open GlobalTheory.StdFrames
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem notOff (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) : ¬ Off S.N.S w := by
  classical
  intro h0
  have h3 := S.N.off w h0
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    exact h3.1 (by rw [G.pl.under_w hv]; exact hv)
  · exact h3.2.1 t ht w h rfl

theorem cpt_supp_zero {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') : cpt w (toEAf D (e + cA D e)) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_add_distrib, map_sum, map_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  obtain ⟨hne, hnc⟩ := GlobalTheory.StdHalfLat.ne_and_not_conj hw (hoff w' hw')
  rw [map_add (f := _), map_add (f := _), (cpt_of_isIdemAt (hes w' hw')).2 w hne,
    (cpt_of_isIdemAt (GlobalTheory.MovedIdem.isIdemAt_conj (hes w' hw') (GlobalTheory.IdemSupport.mem_cP w'))).2 w ?_, add_zero]
  rintro rfl
  apply hnc
  intro c hc
  exact ⟨GlobalTheory.IdemSupport.cO D c, (GlobalTheory.IdemSupport.mem_cP w' c).1 hc, by simp [GlobalTheory.IdemSupport.cO]⟩

theorem map_mt_eq_one {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (mt V g).map ((cpt w).comp (toEAf D)) = 1 := by
  have h0 := cpt_supp_zero hw he hoff
  have h1 : (mt V g - 1).map ((cpt w).comp (toEAf D)) = 0 := by
    ext i j
    rw [Matrix.map_apply, ← hg i j, RingHom.comp_apply, map_mul, map_mul, h0, zero_mul, Matrix.zero_apply]
  have h2 : (mt V g).map ((cpt w).comp (toEAf D)) =
      (mt V g - 1).map ((cpt w).comp (toEAf D)) + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((cpt w).comp (toEAf D)) := by
    rw [← Matrix.map_add _ (map_add _), sub_add_cancel]
  rw [h2, h1, zero_add, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem actO_chi_right (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi j D.R.m) 1 M)⁻¹.1 (G.toPair (.chi j D.R.m) 1 M)⁻¹.2 x =
      (x : Matrix _ _ (AE D)) * mt (G.V (.grid (j + 1) D.R.m)) M := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, inv_one]
  rw [show mt (G.pT (.chi j D.R.m : Pair T)) 1 = 1 from rfl, Matrix.one_mul]
  rfl

theorem actO_chi_left (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.2 x =
      mt (G.V (.grid (j + 1) D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi (j + 1) D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem sub_mul_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin b) (Fin b) K) :
    ((P⁻¹).val * (Y * X) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) * ((Q⁻¹).val * X * Q.val).submatrix (Fin.cast hb) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast hb) (Fin.cast hb) (finCongr hb).bijective]
  congr 1
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem mul_sub_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin a) (Fin a) K) :
    ((P⁻¹).val * (X * Y) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * X * P.val).submatrix (Fin.cast ha) (Fin.cast ha) * ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast ha) (Fin.cast hb) (finCongr ha).bijective]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P.val), Units.mul_inv, Matrix.one_mul]

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = (((loc w β)⁻¹).val * (loc w x).val * (loc w β).val).submatrix (Fin.cast h) (Fin.cast h) := by
  ext i j
  rw [GlobalTheory.FunObj.ProdOpen.inBasis_apply, ← map_inv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt

theorem rowAt_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E), w ∈ locPl G t →
    ∀ (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))) =
    Function.update (Function.update (S.rowAt t w y) j
        (S.rowAt t w y j * @id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k)).val))
      (j + 1) (@id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k))⁻¹.val * S.rowAt t w y (j + 1)) := by
  intro D T L sc G W U S t ht j hj k w hw y
  have hX : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨by omega, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM : (mt _ (moved S j k)).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k)).val := by
    rw [show mt _ (moved S j k) = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1 * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have hM' : (mt _ (moved S j k)⁻¹).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k⁻¹)).val := by
    rw [show mt _ (moved S j k)⁻¹ = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from by
      rw [RowVertexInv.moved]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  funext i

  by_cases h1 : i = j + 1
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos hj, Function.update_self, Frames.coord]
    rw [actO_chi_left, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [← map_inv (inBasis _ (S.B.β (j + 1) D.R.m) w), map_inv (finG (G.V (Node.grid (j + 1) D.R.m))) k, inBasis_val, mul_sub_cast]
    rfl
  by_cases h2 : i = j
  · subst h2
    rw [Function.update_of_ne (by omega), Function.update_self]
    have hj' : i < D.R.m := by omega
    simp only [GridChoice.rowAt, dif_pos hj', Frames.coord]
    rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO_chi_right, Matrix.map_mul, hM]
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [inBasis_val, sub_mul_cast]
    rfl
  · rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
        Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]
    · rw [dite_eq_right hi, dite_eq_right hi]
end GlobalTheory.RowMoveAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchSupportedSmulConjugateUnitarySubOneEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ConjFinArch

variable {D : D7}

def eInf (F : Type) [Field F] [NumberField F] : AF F :=
  ((1 : Ainf F), (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))

theorem one_sub_eInf_fst (F : Type) [Field F] [NumberField F] : (1 - eInf F).1 = 0 := by
  show (1 : Ainf F) - 1 = 0
  exact sub_self _

theorem evI_sub_eInf (F : Type) [Field F] [NumberField F] : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - eInf F) = 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, one_sub_eInf_fst, map_zero]

theorem eInf_smul_tmul (a : AF D.host.F) (y : D.host.E) :
    eInf D.host.F • (a ⊗ₜ[D.host.F] y) = (eInf D.host.F * a) ⊗ₜ[D.host.F] y := by
  rfl

def incInf (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : AF F)
  map_add' x y := by
    show ((x + y, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (x + y, 0 + 0)
    rw [add_zero]
  map_smul' c x := by
    show ((c • x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (c • x, c • (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))
    rw [smul_zero]

theorem eInf_mul' (a : AF D.host.F) : eInf D.host.F * a = incInf D.host.F (fstA D.host.F a) := by
  show ((1 : Ainf D.host.F) * a.1, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * a.2) = (a.1, 0)
  rw [one_mul, zero_mul]

theorem cA_tmul (a : AF D.host.F) (y : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] y) = a ⊗ₜ[D.host.F] D.sp.cm.sig y := by
  show Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig (a ⊗ₜ[D.host.F] y) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem smul_tmul_AF (r a : AF D.host.F) (y : D.host.E) :
    r • (a ⊗ₜ[D.host.F] y) = (r * a) ⊗ₜ[D.host.F] y := rfl

theorem cA_smul (r : AF D.host.F) (x : AF D.host.F ⊗[D.host.F] D.host.E) : cA D (r • x) = r • cA D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a y => rw [smul_tmul_AF, cA_tmul, cA_tmul, smul_tmul_AF]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem eInf_smul (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    eInf D.host.F • x = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  have key : DistribSMul.toLinearMap D.host.F (AF D.host.F ⊗[D.host.F] D.host.E) (eInf D.host.F) =
      (TensorProduct.map (incInf D.host.F) (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E)).comp
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toLinearMap := by
    refine TensorProduct.ext' fun a y => ?_
    show eInf D.host.F • (a ⊗ₜ[D.host.F] y) = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] y))
    rw [eInf_smul_tmul, eInf_mul', Algebra.TensorProduct.map_tmul]
    rfl
  exact LinearMap.congr_fun key x

theorem eInf_smul_eq_zero {x : AF D.host.F ⊗[D.host.F] D.host.E}
    (hx : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x = 0) : eInf D.host.F • x = 0 := by
  rw [eInf_smul, hx, map_zero]

theorem one_apply_map {R S : Type} [Semiring R] [Semiring S] {n : ℕ} (f : R →+* S) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eInf_smul_conjU_sub_one (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hJ : J = c • V.gram) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = 0 := by
  have hm : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = cA D (mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [map_sub, Matrix.sub_apply, one_apply_map]
    rfl
  have hinf : infHom V g = 1 := hg
  have he : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    have := congrArg (fun h : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => h.1 i j) hinf
    exact this
  rw [hm, ← cA_smul, eInf_smul_eq_zero, map_zero]
  rw [map_sub, he]
  exact sub_eq_zero.2 (one_apply_map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom i j).symm

end GlobalTheory.ConjFinArch

theorem GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  intro D V J c hJ g hg u hu
  have h1 : (1 - GlobalTheory.ConjFinArch.eInf D.host.F) * u = 0 := hu _ (GlobalTheory.ConjFinArch.evI_sub_eInf _)
  have h2 : u = u * GlobalTheory.ConjFinArch.eInf D.host.F := by
    rw [sub_mul, one_mul, sub_eq_zero] at h1
    rw [mul_comm]; exact h1
  rw [h2, mul_smul]
  have h3 : GlobalTheory.ConjFinArch.eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.ConjFinArch.eInf_smul_conjU_sub_one V c hJ hg i j, Matrix.zero_apply]
  rw [h3, smul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodinger
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchFam

open scoped Matrix

variable {F : Type} [Field F] [NumberField F]

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV y) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem rho_tens (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {W' : Type} [AddCommGroup W'] [Module (AF F) W']
    {Bf : W' → W' → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (w : W') (hw : At (evI F) w)
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    dc.rho ψ w (tens (evI F) φ r) =
      tens (evI F) (schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) φ) r := by
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add (f := _)]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr x _ ha, hloc, schrF]
  exact (mul_assoc _ _ _).symm

theorem tens_inj {κ : Type} (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evI F) z → r (x + z) = r x)
    (x₀ : κ → AF F) (h0 : r x₀ ≠ 0) (φ₁ φ₂ : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (h : tens (evI F) φ₁ r = tens (evI F) φ₂ r) : φ₁ = φ₂ := by
  funext y
  have hz : At (evI F) (liftV (y - locV x₀)) := at_liftV _
  have hx := congrFun h (x₀ + liftV (y - locV x₀))
  simp only [tens] at hx
  have hl : (fun i => evI F ((x₀ + liftV (y - locV x₀)) i)) = y := by
    change locV (x₀ + liftV (y - locV x₀)) = y
    rw [Coord.loc_add, Coord.loc_lift]
    abel
  rw [hl, hr _ _ hz] at hx
  exact mul_right_cancel₀ h0 hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  M.co.e.symm (liftV v.1, liftV v.2)

theorem at_wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    At (evI F) (wv M v) := by
  intro u hu
  rw [wv, ← map_smul, Prod.smul_mk, at_liftV v.1 u hu, at_liftV v.2 u hu, Prod.mk_zero_zero, map_zero]

theorem at_mul {w : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hw : At (evI F) w) (m : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    At (evI F) (w * m) := by
  intro u hu
  rw [← Matrix.smul_mul, hw u hu, Matrix.zero_mul]

def amap (M : Model σ X W) (m : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (wv M v * m)
  map_add' v v' := by
    simp only [wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add (f := _), Matrix.add_mul,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, Matrix.smul_mul,
      Coord.coordI_smul, RingHom.id_apply]

end GlobalTheory.ArchFam

namespace GlobalTheory.ArchFam

open scoped Matrix


open GlobalTheory.ArchUniq.Coord in
theorem schr_equiv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ v, Continuous fun t => A t v) ∧
      ∀ t v (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
        ⇑(T t f₁) = schrF (trP F (Fin n × Fin d)) (A t v) ⇑(T t f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW γ hγ T hT
  refine ⟨fun t => amap M (mat (γ (Multiplicative.ofAdd t)))ᵀ, fun v => ?_, fun t v f f₁ hf => ?_⟩
  · haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      ((Units.continuous_val.comp continuous_subtype_val).comp (hγ.1.comp continuous_ofAdd)).matrix_transpose
    have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
    have hev : Continuous (evI F) := by
      change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
      refine Continuous.comp ?_ continuous_fst
      change Continuous fun x : InfiniteAdeleRing F =>
        ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
         (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
      refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
      · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
      · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
    have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
    show Continuous fun t => (locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
      locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
    exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp (he.comp (continuous_const.matrix_mul hm))
  · obtain ⟨r₀, hr₀, hinj⟩ := _root_.GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
    have hrr := (hr₀ 0).1
    by_cases hz : ∀ x, r₀ x = 0
    · have h0 : ∀ g : SInf F (Fin n × Fin d), g = 0 := fun g => hinj g 0 (by funext x; simp [tens, hz])
      rw [h0 (T t f₁), h0 (T t f)]
      funext y
      simp [schrF]
    simp only [not_forall] at hz
    obtain ⟨x₀, hx₀⟩ := hz
    have hs := hW.isUSplitting
    have hc : (locV (M.co.e (wv M v)).1, locV (M.co.e (wv M v)).2) = v := coordI_lift M v
    have e1 : tens (evI F) ⇑f₁ r₀ = M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀) := by
      rw [rho_tens ψ hψ M.co _ (at_wv M v) _ _ hrr, hc, ← hf]
    have e2 : om (1, γ (Multiplicative.ofAdd t)) (M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀)) =
        M.co.rho ψ (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)
          (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀)) := by
      rw [hs.impl (1, γ (Multiplicative.ofAdd t)) (wv M v) _ (hr₀ f).2]
      congr 2
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
    have e3 := hT t f r₀ (hr₀ f)
    have e4 := hT t f₁ r₀ (hr₀ f₁)
    apply tens_inj r₀ hrr x₀ hx₀
    rw [← e4, e1, e2, e3, rho_tens ψ hψ M.co _ (at_mul (at_wv M v) _) _ _ hrr]
    rfl

end GlobalTheory.ArchFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanPoint_pureTensor_keeps_finiteFactor : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  first | exact @GlobalTheory.ArchPure.pure_arch | exact GlobalTheory.ArchPure.pure_arch | (intros; apply GlobalTheory.ArchPure.pure_arch <;> assumption)
end

