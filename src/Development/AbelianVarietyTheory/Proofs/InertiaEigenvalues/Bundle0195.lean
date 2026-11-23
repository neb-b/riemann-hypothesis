module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisin
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_E_smul_EN_mem_Man : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι),
    ∃ n : ℕ, ∀ m ∈ P.M, E K l e ^ n • P.EN m ∈ P.Man := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  have hk : 1 / ((e : ℝ) * l) < 1 / (e : ℝ) := by
    have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact one_div_lt_one_div_of_lt he (by nlinarith)

  have hL : ∀ v ∈ P.L, E K l e ^ α • P.conn v ∈ P.Man := by
    intro v hv
    have hv' : v ∈ P.Lk (1 / (e : ℝ)) := P.ext_mono (A_le_Rpi l e) hv
    obtain ⟨w, rfl⟩ := P.xiExt.surjective v
    have hw : w ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      (_root_.GlobalTheory.BK.xiExt_mem_Lk_iff O K l e a ι P (1 / (e : ℝ)) hk w).1 hv'
    have hNw : (fun τ i => N K (w τ i)) ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      mem_tot.2 fun τ i => N_mem (derivative_mem_R l (mem_tot.1 hw τ i))
    have h1 : P.conn (P.xiExt w) ∈ P.ext (Rpi O K l e) := by
      rw [PhiMod.conn_xiExt]
      exact (_root_.GlobalTheory.BK.xiExt_mem_Lk_iff O K l e a ι P (1 / (e : ℝ)) hk _).2 hNw
    exact P.smul_mem_Mext_of_basis (fun i => hα _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_Rpi l e) h1
  refine ⟨α + β, fun m hm => ?_⟩
  have hv := hL _ (hβ m hm)
  rw [PhiMod.conn_smul, smul_add, smul_smul, smul_smul, ← pow_add] at hv
  have h2 : (E K l e ^ α * N K (E K l e ^ β)) • m ∈ P.Man :=
    P.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) α) (N_mem (derivative_mem_R l (pow_mem (E_mem l e _) β))))
      (P.M_le_Man hm)
  have h3 : E K l e ^ (α + β) • P.conn m ∈ P.Man := by
    have := sub_mem hv h2
    rwa [add_sub_cancel_left] at this
  rw [PhiMod.EN_apply, smul_comm]
  exact P.smul_mem_Man (E_mem l e _) h3

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValue
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.Enlarge

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {g : Ω} (hg : g ∈ Algebra.adjoin K gs) :
    ∃ d : O, d ≠ 0 ∧ algebraMap K Ω (algebraMap O K d) * g ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨(1 : O), one_ne_zero, ?_⟩
    rw [map_one, map_one, one_mul]
    exact Subring.subset_closure (Set.mem_union_right _ hx)
  | algebraMap x =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    have hb' : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    rw [← map_mul, mul_div_cancel₀ _ hb']
    exact hOS a
  | add x y _ _ hx hy =>
    obtain ⟨d1, h1, hx⟩ := hx
    obtain ⟨d2, h2, hy⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have : algebraMap K Ω (algebraMap O K (d1 * d2)) * (x + y) =
        algebraMap K Ω (algebraMap O K d2) * (algebraMap K Ω (algebraMap O K d1) * x) +
          algebraMap K Ω (algebraMap O K d1) * (algebraMap K Ω (algebraMap O K d2) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact S.add_mem (S.mul_mem (hOS _) hx) (S.mul_mem (hOS _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨d1, h1, hx⟩ := hx
    obtain ⟨d2, h2, hy⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have : algebraMap K Ω (algebraMap O K (d1 * d2)) * (x * y) =
        (algebraMap K Ω (algebraMap O K d1) * x) * (algebraMap K Ω (algebraMap O K d2) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact S.mul_mem hx hy

theorem clear_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {r : Ω} (hr : IsIntegral (Algebra.adjoin K gs) r) :
    ∃ κ : O, κ ≠ 0 ∧ ∃ q : Polynomial Ω, q.Monic ∧ q.eval (algebraMap K Ω (algebraMap O K κ) * r) = 0 ∧
      ∀ i, q.coeff i ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hr
  have hex := fun i => exists_den (O := O) gs (p.coeff i).2
  choose d hd0 hd using hex
  set κ : O := ∏ i ∈ Finset.range (p.natDegree + 1), d i with hκdef
  have hκ : κ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i)
  have hκc : ∀ i, algebraMap K Ω (algebraMap O K κ) * ((p.coeff i : Algebra.adjoin K gs) : Ω) ∈ S := by
    intro i
    by_cases hi : i ∈ Finset.range (p.natDegree + 1)
    · rw [hκdef, ← Finset.mul_prod_erase _ _ hi, map_mul, map_mul, mul_comm (algebraMap K Ω (algebraMap O K (d i))),
        mul_assoc]
      exact S.mul_mem (hOS _) (hd i)
    · have : p.coeff i = 0 := p.coeff_eq_zero_of_natDegree_lt (by simp at hi; omega)
      rw [this]
      simp
  set k := algebraMap K Ω (algebraMap O K κ) with hk
  set pm := p.map (algebraMap (Algebra.adjoin K gs) Ω) with hpmdef
  have hpmm : pm.Monic := hpm.map _
  have hdeg : pm.natDegree = p.natDegree := hpm.natDegree_map _
  refine ⟨κ, hκ, pm.scaleRoots k, (monic_scaleRoots_iff k).mpr hpmm, ?_, ?_⟩
  · have h0 : eval₂ (RingHom.id Ω) r pm = 0 := by
      rw [eval₂_id, hpmdef, Polynomial.eval_map]; exact hp
    have := scaleRoots_eval₂_eq_zero (RingHom.id Ω) h0 (s := k)
    rwa [eval₂_id] at this
  · intro i
    rw [coeff_scaleRoots]
    have hci : pm.coeff i = ((p.coeff i : Algebra.adjoin K gs) : Ω) := by
      rw [hpmdef, coeff_map]; rfl
    rcases h : pm.natDegree - i with _ | m
    · rcases (show pm.natDegree ≤ i by omega).lt_or_eq with hlt | heq
      · rw [coeff_eq_zero_of_natDegree_lt hlt]; simp
      · rw [← heq, hpmm.coeff_natDegree]; simp
    · have : pm.coeff i * k ^ (m + 1) = k ^ m * (k * ((p.coeff i : Algebra.adjoin K gs) : Ω)) := by
        rw [hci]; ring
      rw [this]
      exact S.mul_mem (S.pow_mem (hOS κ) m) (hκc i)

theorem mem_of_root {K Ω L : Type} [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (A : Subalgebra K Ω)
    (Sb : Subring Ω) (hSA : ∀ x ∈ Sb, x ∈ A) (ψ : A →ₐ[K] L) (W : ValuationSubring L)
    (hW : ∀ x (hx : x ∈ Sb), ψ ⟨x, hSA x hx⟩ ∈ W) (q : Polynomial Ω) (hqm : q.Monic) (hqc : ∀ i, q.coeff i ∈ Sb)
    (t : Ω) (ht : t ∈ A) (h0 : q.eval t = 0) : ψ ⟨t, ht⟩ ∈ W := by
  let incl : Sb →+* A :=
    { toFun := fun x => ⟨x, hSA x x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let θ : Sb →+* W := ((ψ : A →+* L).comp incl).codRestrict W (fun x => hW x x.2)
  have hcs : (q.coeffs : Set Ω) ⊆ Sb := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact hqc n
  set q' := q.toSubring Sb hcs with hq'
  have hq'm : q'.Monic := (Polynomial.monic_toSubring q Sb hcs).mpr hqm
  have hroot : Polynomial.eval₂ incl ⟨t, ht⟩ q' = 0 := by
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ q' incl ((A.val : A →ₐ[K] Ω) : A →+* Ω) ⟨t, ht⟩
    rw [show ((A.val : A →ₐ[K] Ω) : A →+* Ω).comp incl = Sb.subtype from RingHom.ext fun _ => rfl,
      Polynomial.eval₂_eq_eval_map Sb.subtype, hq', Polynomial.map_toSubring] at key
    change ((A.val : A →ₐ[K] Ω) : A →+* Ω) _ = 0
    rw [key]
    exact h0
  have hint : IsIntegral W (ψ ⟨t, ht⟩) := by
    refine ⟨q'.map θ, hq'm.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap W L).comp θ = (ψ : A →+* L).comp incl := RingHom.ext fun _ => rfl
    rw [hc]
    have h1 := Polynomial.hom_eval₂ q' incl (ψ : A →+* L) ⟨t, ht⟩
    rw [hroot, map_zero] at h1
    exact h1.symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hw]
  exact w.2

def trPt {Ω : Type} [Field Ω] [Algebra c.F Ω] {A B : Subalgebra c.F Ω} (h : A = B) (y : FrPt Xo c A) :
    FrPt Xo c B :=
  h ▸ y

theorem frMap_trPt {Ω : Type} [Field Ω] [Algebra c.F Ω] {A B : Subalgebra c.F Ω} (h : A = B) {T : Type} [CommRing T]
    [Algebra c.F T] (ψ : B →ₐ[c.F] T) (y : FrPt Xo c A) (z : FrPt Xo c T) :
    FrMap ψ (trPt h y) z ↔ FrMap (ψ.comp (Subalgebra.equivOfEq A B h).toAlgHom) y z := by
  subst h
  have : ψ.comp (Subalgebra.equivOfEq A A rfl).toAlgHom = ψ := AlgHom.ext fun _ => rfl
  rw [this]
  rfl

variable {O : Type} [CommRing O] {β : O →+* c.F}

attribute [local instance] Classical.propDecidable

theorem eqR (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) (e : P.Ω) (he : e ∈ P.es) :
    P.R e = Algebra.adjoin c.F (insert e⁻¹ ((insert s P.gens : Finset P.Ω) : Set P.Ω)) := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.insert_subset_insert (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
  · rw [Algebra.adjoin_le_iff, Finset.coe_insert]
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · exact hs e he
    · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

def enlarge (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) : PChart Xo c β where
  Ω := P.Ω
  fld := P.fld
  alg := P.alg
  gens := insert s P.gens
  frac := by
    rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
  es := P.es
  es_ne := P.es_ne
  es_mem e he := ⟨(P.es_mem e he).1, Subring.closure_mono
    (Set.union_subset_union_right _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)) (P.es_mem e he).2⟩
  sm e he := by rw [← eqR P s hs e he]; exact P.sm e he
  yg := P.yg
  y e he := trPt (eqR P s hs e he) (P.y e he)
  gen e he := by
    rw [frMap_trPt]
    have : (Algebra.adjoin c.F (insert e⁻¹ ((insert s P.gens : Finset P.Ω) : Set P.Ω))).val.comp
        (Subalgebra.equivOfEq _ _ (eqR P s hs e he)).toAlgHom = (P.R e).val := AlgHom.ext fun _ => rfl
    rw [this]
    exact P.gen e he
  int e he T io := by
    intro ψ hO hg z hz
    letI : Algebra c.F T.Fr := io.toAlgebra
    exact P.int e he T io (ψ.comp (Subalgebra.equivOfEq (P.R e) _ (eqR P s hs e he)).toAlgHom) hO
      (fun g hgm => hg _ (Finset.mem_insert_of_mem hgm)) z ((frMap_trPt (eqR P s hs e he) ψ (P.y e he) z).mp hz)

theorem catches_enlarge (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) {L : Type} [Field L]
    [Algebra c.F L] (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (q : Polynomial P.Ω)
    (hqm : q.Monic) (hq0 : q.eval s = 0) (hqc : ∀ i, q.coeff i ∈ P.B) (y : FrPt Xo c L) (hy : P.Catches W y) :
    (enlarge P s hs).Catches W y := by
  obtain ⟨e, he, ψ, z, t, hg, hm, hb⟩ := hy
  have hR := eqR P s hs e he
  refine ⟨e, he, ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom, z, t, ?_, ?_, hb⟩
  · intro g hgm
    rcases Finset.mem_insert.mp hgm with h | h
    · have hBA : ∀ x ∈ P.B, x ∈ P.R e := by
        intro x hx
        refine (Subring.closure_le (t := (P.R e).toSubring)).mpr ?_ hx
        rintro x (⟨a, rfl⟩ | hx)
        · exact Subalgebra.algebraMap_mem _ _
        · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
      have hWB : ∀ x (hx : x ∈ P.B), ψ ⟨x, hBA x hx⟩ ∈ W := by
        intro x hx
        have hle : P.B ≤ ((W.toSubring.comap (ψ : P.R e →+* L)).map ((P.R e).val : P.R e →+* P.Ω)) := by
          rw [Subring.closure_le]
          rintro x (⟨a, rfl⟩ | hx)
          · refine ⟨algebraMap c.F (P.R e) (β a), ?_, rfl⟩
            show ψ (algebraMap c.F (P.R e) (β a)) ∈ W
            rw [AlgHom.commutes]; exact hW a
          · exact ⟨⟨x, Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)⟩, hg _ hx, rfl⟩
        obtain ⟨a, ha, hax⟩ := hle hx
        have : a = ⟨x, hBA x hx⟩ := Subtype.ext hax
        subst this
        exact ha
      have hgR : (show P.Ω from g.1) ∈ P.R e := by rw [hR]; exact g.2
      exact mem_of_root (P.R e) P.B hBA ψ W hWB q hqm hqc (show P.Ω from g.1) hgR (by rw [h]; exact hq0)
    · exact hg (Subalgebra.equivOfEq _ _ hR.symm g) h
  · have : (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom).comp (Subalgebra.equivOfEq _ _ hR).toAlgHom = ψ :=
      AlgHom.ext fun _ => rfl
    exact (frMap_trPt hR (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom) (P.y e he) z).mpr
      (by rw [this]; exact hm)

theorem enlarge_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ f P hR hI
  obtain ⟨κ, hκ, q, hqm, hq0, hqc⟩ := clear_den (O := O) (P.gens : Set P.Ω) hI
  have hk : algebraMap O c.F κ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hκ)
  set r := evR Xo c f P.yg with hr
  set s := algebraMap c.F P.Ω (algebraMap O c.F κ) * r with hsdef
  have hs : ∀ e ∈ P.es, s ∈ P.R e := fun e he =>
    Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hR e he)
  refine ⟨enlarge P s hs, ?_, fun L _ _ W hW y hy => catches_enlarge P s hs W hW q hqm hq0 hqc y hy⟩
  show r ∈ Algebra.adjoin c.F ((insert s P.gens : Finset P.Ω) : Set P.Ω)
  have : r = algebraMap c.F P.Ω (algebraMap O c.F κ)⁻¹ * s := by
    rw [hsdef, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
  rw [this]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin (by simp))

end GlobalTheory.Reg.Enlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewton
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.IdemLift

open Filter Topology

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

noncomputable def step (y : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  y * y + y * y + y * y - (y * y * y + y * y * y)

noncomputable def seq (x : Matrix (Fin n) (Fin n) E) : ℕ → Matrix (Fin n) (Fin n) E
  | 0 => x
  | k + 1 => step (seq x k)

theorem step_sq (y : Matrix (Fin n) (Fin n) E) :
    step y * step y - step y = (y * y - y) * (y * y - y) *
      ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)) := by
  unfold step; noncomm_ring

theorem step_sub (y : Matrix (Fin n) (Fin n) E) :
    step y - y = (y * y - y) * (1 - (y + y)) := by
  unfold step; noncomm_ring

theorem step_integ {y : Matrix (Fin n) (Fin n) E} (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖step y i j‖ ≤ 1 := by
  have h2 := integ_mul hy hy
  have h3 := integ_mul h2 hy
  exact integ_sub (integ_add (integ_add h2 h2) h2) (integ_add h3 h3)

theorem step_comm {y N : Matrix (Fin n) (Fin n) E} (h : y * N = N * y) :
    step y * N = N * step y := by
  have hc : Commute y N := h
  have h2 := hc.mul_left hc
  have h3 := h2.mul_left hc
  exact ((h2.add_left h2).add_left h2).sub_left (h3.add_left h3)

theorem seq_inv (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    (∀ i j, ‖seq x k i j‖ ≤ 1) ∧ seq x k * N = N * seq x k ∧
      ∃ b : Matrix (Fin n) (Fin n) E, (∀ i j, ‖b i j‖ ≤ 1) ∧
        seq x k * seq x k - seq x k = ϖ ^ (2 ^ k) • b := by
  induction k with
  | zero => exact ⟨hx, hxN, a, ha, by simpa [seq] using hxa⟩
  | succ k ih =>
    obtain ⟨hi, hc, b, hb, hd⟩ := ih
    refine ⟨step_integ hi, step_comm hc, ?_⟩
    set y := seq x k
    have hdi : ∀ i j, ‖(y * y - y) i j‖ ≤ 1 := integ_sub (integ_mul hi hi) hi
    refine ⟨b * b * ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)),
      integ_mul (integ_mul hb hb) (integ_sub (integ_add (integ_add (integ_add hdi hdi) hdi) hdi)
        (integ_add (integ_add integ_one integ_one) integ_one)), ?_⟩
    show step y * step y - step y = _
    rw [step_sq, hd, smul_mul_smul_comm, smul_mul_assoc, ← pow_add, pow_succ, mul_two]

theorem seq_succ_sub (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x (k + 1) - seq x k) i j‖ ≤ ‖ϖ‖ ^ (2 ^ k) := by
  obtain ⟨hi, -, b, hb, hd⟩ := seq_inv x N a ϖ hxN hx ha hxa k
  intro i j
  have hc : ∀ i j, ‖(b * (1 - (seq x k + seq x k))) i j‖ ≤ 1 :=
    integ_mul hb (integ_sub integ_one (integ_add hi hi))
  show ‖(step (seq x k) - seq x k) i j‖ ≤ _
  rw [step_sub, hd, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (hc i j)

theorem seq_sub_le (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x k - x) i j‖ ≤ ‖ϖ‖ := by
  induction k with
  | zero => intro i j; simp [seq]
  | succ k ih =>
    intro i j
    have h1 := seq_succ_sub x N a ϖ hxN hx ha hxa k i j
    have h2 : ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ := by
      calc ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.one_le_two_pow)
        _ = ‖ϖ‖ := pow_one _
    have : (seq x (k + 1) - x) i j = (seq x (k + 1) - seq x k) i j + (seq x k - x) i j := by
      simp [Matrix.sub_apply]
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans h2) (ih i j))

theorem idem_lift (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E]
    (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E) :
    ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a →
    ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧
      (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  intro hϖ hxN hx ha hxa
  have hinv := seq_inv x N a ϖ hxN hx ha hxa
  have hpow : ∀ k : ℕ, ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ k := fun k =>
    pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.lt_two_pow_self).le
  have hcs : ∀ i j, CauchySeq (fun k => seq x k i j) := by
    intro i j
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 hϖ (fun k => ?_)
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (seq_succ_sub x N a ϖ hxN hx ha hxa k i j).trans (hpow k)
  choose e he using fun i j => cauchySeq_tendsto_of_complete (hcs i j)
  have hT : Tendsto (seq x) atTop (𝓝 (Matrix.of e)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => he i j

  have heN : Matrix.of e * N = N * Matrix.of e := by
    have hcl : IsClosed {M : Matrix (Fin n) (Fin n) E | M * N = N * M} :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    exact hcl.mem_of_tendsto hT (Eventually.of_forall fun k => (hinv k).2.1)

  have heI : ∀ i j, ‖Matrix.of e i j‖ ≤ 1 := fun i j =>
    le_of_tendsto' (he i j).norm fun k => (hinv k).1 i j

  have hee : Matrix.of e * Matrix.of e = Matrix.of e := by
    have hD : Tendsto (fun k => seq x k * seq x k - seq x k) atTop
        (𝓝 (Matrix.of e * Matrix.of e - Matrix.of e)) := (hT.mul hT).sub hT
    rw [← sub_eq_zero]
    ext i j
    have h1 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop
        (𝓝 ((Matrix.of e * Matrix.of e - Matrix.of e) i j)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hD i) j
    have h0 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg ϖ) hϖ)
      obtain ⟨-, -, b, hb, hd⟩ := hinv k
      rw [hd, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (by positivity) (hb i j)).trans (hpow k)
    simpa using tendsto_nhds_unique h1 h0

  have hex : ∀ i j, ‖(Matrix.of e - x) i j‖ ≤ ‖ϖ‖ := by
    intro i j
    have h1 : Tendsto (fun k => (seq x k - x) i j) atTop (𝓝 ((Matrix.of e - x) i j)) := by
      simpa [Matrix.sub_apply] using (he i j).sub_const (x i j)
    exact le_of_tendsto' h1.norm fun k => seq_sub_le x N a ϖ hϖ hxN hx ha hxa k i j
  by_cases h0 : ϖ = 0
  · have hz : Matrix.of e - x = 0 := by
      ext i j
      have := hex i j
      rw [h0, norm_zero] at this
      simpa using norm_le_zero_iff.1 this
    refine ⟨Matrix.of e, 0, heN, by simp, hee, heI, integ_zero, ?_⟩
    rw [hz, smul_zero]
  · refine ⟨Matrix.of e, ϖ⁻¹ • (Matrix.of e - x), heN, ?_, hee, heI, ?_, ?_⟩
    · rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, heN, hxN]
    · intro i j
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      exact inv_mul_le_one_of_le₀ (hex i j) (norm_nonneg _)
    · rw [smul_inv_smul₀ h0]

end GlobalTheory.IdemLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomial
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.GenKernelFit

theorem aeval_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (p : Polynomial k) : ∀ y ∈ Q, Polynomial.aeval T p y ∈ Q := by
  first
  | exact @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main ..)

theorem apply_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (f : Polynomial k) (hf : f.eval 0 ≠ 0) (x : U)
    (h1 : T (Polynomial.aeval T f x) ∈ Q) (j : ℕ) (h2 : (T ^ j) x ∈ Q) : T x ∈ Q := by
  have hc : IsCoprime f Polynomial.X := by
    refine ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_).symm
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hf
  obtain ⟨a, b, hab⟩ := hc.pow_right (n := j)
  have e : (Polynomial.X : Polynomial k) =
      a * (Polynomial.X * f) + b * (Polynomial.X * Polynomial.X ^ j) := by
    linear_combination (-Polynomial.X) * hab
  have e2 : T x = Polynomial.aeval T a (T (Polynomial.aeval T f x)) + Polynomial.aeval T b (T ((T ^ j) x)) := by
    have := congrArg (fun p => Polynomial.aeval T p x) e
    simpa only [map_add (f := _), map_mul, map_pow, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply]
      using this
  rw [e2]
  exact Q.add_mem (aeval_mem T Q hQ a _ h1) (aeval_mem T Q hQ b _ (hQ _ h2))

theorem nab_mem_of_ePoly : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  intro k _ l n m _ _ _ R D i N s hC hE x hx hj
  obtain ⟨f, hf, hE⟩ := hE
  obtain ⟨j, hj⟩ := hj
  exact apply_mem (nab (D.γ i)) ((sh s N).restrictScalars k)
    (GlobalTheory.PhiGam.condC_sh_and_nab_mem R (D.γ i) (D.γ_semi i) N hC s).2 f hf x (hE x hx) j hj

end GlobalTheory.GenKernelFit
end

