module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPureTensorSumDatumRouteThroughSmallVertex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKsCocOfKsRel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSCechData

open GlobalTheory.KS GlobalTheory.LogKSBal

theorem constFn_spMap {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {Y : Scheme.{0}} (q : Y ⟶ Sp K)
    (O : Y.Opens) (r : R) : constFn (q ≫ spMap x₀) O r = constFn q O (x₀ r) := by
  refine ext_valR _ _ fun B _ y hy => ?_
  have e : y ≫ q = spMap (Spec.preimage (y ≫ q)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ q)).hom = β at e
  rw [valR_constFn q y hy e, valR_constFn (q ≫ spMap x₀) y hy (β := β.comp x₀)
    (by rw [← Category.assoc, e, GlobalTheory.LogKSLoc.spMap_comp'])]
  rfl

theorem constFn_neg {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (r : K) :
    constFn q O (-r) = -constFn q O r := by
  simp [constFn]

theorem exists_ksCoc_of_ksRel : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := by
  intro R _ K _ x₀ P A _ m hm g e dd he hdd D M hKS
  obtain ⟨J, W, j, d, hcov, hWj, hlift, hdiff⟩ := hKS
  have := P.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hloc : ∀ x : P.A.left, ∃ (Ω : P.A.left.Opens) (k : J), IsAffineOpen Ω ∧ x ∈ Ω ∧ Ω ≤ W k := by
    intro x
    have h2 : x ∈ ⨆ k, W k := by
      rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨_, ⟨Ω, hΩ, rfl⟩, hx, hle⟩ := P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (W k).isOpen
    exact ⟨Ω, k, hΩ, hx, hle⟩
  obtain ⟨s, hfin, Ω, κ, hΩ, hΩW, hs⟩ : ∃ (s : Type) (_ : Finite s) (Ω : s → P.A.left.Opens) (κ : s → J),
      (∀ a, IsAffineOpen (Ω a)) ∧ (∀ a, Ω a ≤ W (κ a)) ∧ ⨆ a, Ω a = ⊤ := by
    choose Ω κ hΩ hxΩ hΩW using hloc
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Ω x : Set P.A.left))
      (fun x => (Ω x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxΩ x⟩)
    refine ⟨s, inferInstance, fun a => Ω a, fun a => κ a, fun a => hΩ a, fun a => hΩW a, top_le_iff.1 fun x _ => ?_⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  have hle : ∀ a : s, Ω a ≤ P.L.U (j (κ a)) := fun a => (hΩW a).trans (hWj (κ a))
  let L := GlobalTheory.FinAffineCharts.refineLB P.L Ω (fun a => j (κ a)) hle
  have happ : ∀ (O : P.A.left.Opens) (f : Γ(P.A.left, O)), (m.app O).hom f = pbT m f (m ⁻¹ᵁ O) :=
    fun O f => GlobalTheory.KS.AdjDlog.app_eq_pbT m O f
  have hconst : ∀ (O : P.A.left.Opens) (r : R), pbT m (constFn P.A.hom O r) (m ⁻¹ᵁ O) =
      constFn A.hom (m ⁻¹ᵁ O) (x₀ r) := fun O r => by
    rw [pbT_constFn _ _ le_rfl, hm, constFn_spMap]
  refine ⟨L, hfin, GlobalTheory.FinAffineCharts.refineLB_isLB P.isLB _ _ hle hs,
    fun a => hΩ a, GlobalTheory.FinAffineCharts.iso_refineLB P.isLB _ _ hle,
    fun a O f => pbT m (d (κ a) O f) _, fun φ hφ => ⟨fun a => ⟨fun O hO f f' => ?_, fun O hO f f' => ?_,
      fun O O' h hO f => ?_, fun O hO r => ?_⟩, fun a b O hO f => ?_⟩⟩
  · rw [(hlift _).1.1 _ (hO.trans (hΩW a)), pbT_add]
  · rw [(hlift _).1.2.1 _ (hO.trans (hΩW a)), pbT_add, pbT_mul, pbT_mul, happ, happ]
  · rw [(hlift _).1.2.2 _ _ h (hO.trans (hΩW a)), ← rsT_of_le h, pbT_rsT _ h le_rfl,
      rsT_pbT _ le_rfl (m.preimage_mono h)]
  · rw [(hlift _).2 _ (hO.trans (hΩW a)), hconst]
  · have hO' : O ≤ Ω a ⊓ Ω b := hO
    have hU : Ω a ⊓ Ω b ≤ P.L.U (j (κ a)) ⊓ P.L.U (j (κ b)) := inf_le_inf (hle a) (hle b)
    have hab : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b := m.preimage_mono hO
    have hab' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ (Ω a ⊓ Ω b) := m.preimage_mono hO
    have hg : (L.g a b).val = rsT (P.L.g (j (κ a)) (j (κ b))).val (Ω a ⊓ Ω b) :=
      GlobalTheory.KS.AdjDlog.val_res hU _
    have hφ' : ∀ c, rsT (φ c a b) (m ⁻¹ᵁ O) =
        pbT m (dlg P.A (𝟙 P.A.left) P.L (e c) (j (κ a)) (j (κ b)) O) (m ⁻¹ᵁ O) := fun c => by
      have h₁ : pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b =
          pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b)) :=
        (hφ c a b).trans ((congrArg (dd c (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (happ (Ω a ⊓ Ω b) (L.g a b).val).symm).trans
          (hdd c (Ω a ⊓ Ω b) (L.g a b).val))
      have h₂ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b) (m ⁻¹ᵁ O) =
          rsT (pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (m ⁻¹ᵁ O) :=
        congrArg (rsT · (m ⁻¹ᵁ O)) h₁
      have h₃ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) (m ⁻¹ᵁ O) =
          pbT m (P.L.g (j (κ a)) (j (κ b))).val (m ⁻¹ᵁ O) :=
        (rsT_pbT m (O₀ := Ω a ⊓ Ω b) (fun p hp => hp) hab _).trans
          ((congrArg (pbT m · (m ⁻¹ᵁ O)) hg).trans (pbT_rsT m hU hab' _))
      have h₄ : rsT (e c (Ω a ⊓ Ω b) (L.g a b).val) O = e c O (rsT (P.L.g (j (κ a)) (j (κ b))).val O) := by
        refine (rsT_of_le hO' _).trans (((he c).2.2 _ _ hO' le_top _).symm.trans (congrArg (e c O) ?_))
        refine (rsT_of_le (O₀ := Ω a ⊓ Ω b) hO' _).symm.trans ?_
        rw [← rsT_rsT hU hO']
        exact congrArg (fun z => rsT z O) hg
      rw [rsT_mul, h₃, rsT_pbT m le_rfl hab', ← pbT_rsT m hO' le_rfl, h₄] at h₂
      rw [dlg, GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), pbT_mul, ← h₂,
        pbT_rsT m (hO'.trans hU) le_rfl, mul_right_comm, ← pbT_mul, Units.mul_inv,
        pbT_one m (m.preimage_mono (hO'.trans hU)), _root_.one_mul]
    have key := hdiff (κ a) (κ b) O (hO'.trans (inf_le_inf (hΩW a) (hΩW b))) f
    rw [← pbT_sub, ← neg_sub, key, pbT_neg, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hdd, lc, rsT_sum, Finset.sum_mul, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [rsT_mul, rsT_constFn _ hab, hφ', pbT_mul, pbT_mul, hconst, constFn_neg]
    ring

end GlobalTheory.KSCechData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocTuplesThetaOfAdm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.exists_locTuples_theta_of_adm : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ (∀ j, OrdGe M T ξ (t k j) a) ∧ ∃ j, OrdEq M T ξ (t k j) a := by
  intro g n hg hn hodd F φ hφ W hW o' Ω _ _ _ _ S ρ u hBig hSharp hgen
  have hNodd : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN2 := S.N_ge
  have hN3 : 3 ≤ S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  have hn2 : ρ.n ≠ 2 := by
    intro h2; have := ρ.n_odd; rw [h2] at this; exact (Nat.not_odd_iff_even.2 even_two) this
  have hε : ∃ ε : Fin 8 → ℤ, Nat.Coprime S.N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
    rw [ρ.N_eq]; exact GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow W hW ρ.n ρ.k ρ.n_prime hn2
  have hC := _root_.GlobalTheory.Poinc.finite_types g φ hφ W hW.1 S.N hN3 hε
  choose ιf 𝓛f hιf using fun R : Fin (g + 1) => hC R.1 (Nat.lt_succ_iff.1 R.2)
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup S.Gam, (T₀ →+ ZMod S.N) × (S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) × S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set Ω := {v | v ≠ 0} ∩ Set.range (fun d : Dt => S.FF d.1 d.2.1 d.2.2.1 / S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let mult : Fin (g + 1) → ℕ := fun R => ∏ s ∈ Finset.univ.erase R, ιf s
  let K := Σ R : Fin (g + 1), Σ _ : {L // L ∈ 𝓛f R}, ((Fin 8 → Fin R.1 → ZMod S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → Ω := fun k j => ∏ c, ((k.2.2 c : Es) : Ω) ^ ((mult k.1 : ℤ) * j.1 c)
  refine ⟨∏ R, ιf R, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun R _ => by have := (hιf R).1; omega)
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun c _ => zpow_ne_zero _ (k.2.2 c).2.1
  intro M U₀ EE FinalForm hAdm hEE x
  obtain ⟨r, b₀, μ, e, hr, hsym, hpos, hμ, hmin, he, htr⟩ :=
    _root_.GlobalTheory.Poinc.local_lattice_orders g n hg hn hodd F W hW o' Ω S ρ u hBig hSharp hgen hN0 M U₀ EE FinalForm hAdm hEE x
  let R : Fin (g + 1) := ⟨r, by omega⟩
  obtain ⟨hιR, hL⟩ := hιf R
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hsym hpos μ hμ hmin
  have heE : ∀ c, e c ∈ Es := fun c => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he c
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨R, ⟨L, hLmem⟩, fun c => ⟨e c, heE c⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec

  set b' := T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap with hb'
  have hb'sym : ∀ x y, b' x y = b' y x := fun x y => T.symm _ _
  have hb'psd : ∀ x, 0 ≤ b' x x := _root_.GlobalTheory.Poinc.psd_of_min (N := S.N) (by omega) W hW b' (μ 0) fun α hα =>
    hπmin 0 α fun u i => by obtain ⟨m, hm⟩ := hα u i; simp [hm, hμ]
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'sym hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.β := by
    have hpull : pull π.toIntLinearMap T.β = b' := LinearMap.ext₂ fun _ _ => rfl
    rw [← hpull]; exact evalZ_pull φ (r := π.toIntLinearMap) hπs T.β
  have hφ0 : 0 ≤ φ.evalZ b' :=
    (hφ (Fin r → ℤ) (by rw [Module.finrank_fin_fun]; exact hr)).evalZ_nonneg (mem_balForms_int.2 hb'sym) hb'psd

  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    rw [hz₀, hy, ← hξ₀]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup S.Gam) c' κ, S.FF T₀ c' κ ∈ S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))
  have hunit : ∀ c, e c ≠ 0 ∧ e c ∈ M.O z₀ ∧ (e c)⁻¹ ∈ M.O z₀ := by
    intro c
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he c
    rw [hc] at hne ⊢
    have hF : S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ c, M.val y (e c) ≠ 0 := by
    intro c
    have h1 := RatModel.val_mul (M := M) hsp (hunit c).2.1 (hunit c).2.2
    rw [mul_inv_cancel₀ (hunit c).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ c, M.val y (e c ^ S.N) = M.val y (e c) ^ S.N := by
    intro c
    have := _root_.GlobalTheory.Poinc.RatModel.val_prod_zpow M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e c) (fun _ => (S.N : ℤ)) fun _ => hunit c
    simpa using this
  choose v w hvw using fun c => _root_.GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit T.irr (M.val y (e c)) (hvne c)

  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ c, (S.N : ℤ) * v c = qW W b' (μ c) := by
    intro c
    obtain ⟨hq0, w', hw'⟩ := hq c
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((S.N : ℤ) * v c) *
        algebraMap T.V (FractionRing T.V) ((w c ^ (S.N : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ (((qW W b' (μ c)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (S.N : ℤ) (v c), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw c, hw',
        map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  have hmR : (∏ R', ιf R') = ιf R * mult R := (Finset.mul_prod_erase Finset.univ ιf (Finset.mem_univ R)).symm
  let E : ((Fin 8 → Fin r → ZMod S.N) → ℤ) → ℤ := fun ν => ∑ c, v c * ((mult R : ℤ) * ν c)
  have hE : ∀ ν, (S.N : ℝ) * (E ν : ℝ) = (mult R : ℝ) * ∑ c, (ν c : ℝ) * (qW W b' (μ c) : ℝ) := by
    intro ν
    simp only [E, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hNv c]; push_cast; ring
  have hzs : ∀ (f : (Fin 8 → Fin r → ZMod S.N) → ℤ) (s : Finset (Fin 8 → Fin r → ZMod S.N)),
      ∏ c ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f c = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ c ∈ s, f c := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ c, e c ^ ((mult R : ℤ) * ν c)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ E ν *
      algebraMap T.V (FractionRing T.V) ((∏ c, w c ^ ((mult R : ℤ) * ν c) : T.Vˣ) : T.V) := by
    intro ν
    rw [_root_.GlobalTheory.Poinc.RatModel.val_prod_zpow M y z₀ hsp _ _ _ fun c => hunit c]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin 8 → Fin r → ZMod S.N) → ℤ, (∏ c, e c ^ ((mult R : ℤ) * ν c)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun c _ => ?_
    rcases Int.eq_nat_or_neg ((mult R : ℤ) * ν c) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit c).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit c).2.2 k
  have hιeq : ((∏ R', ιf R' : ℕ) : ℝ) = (ιf R : ℝ) * mult R := by rw [hmR]; push_cast; ring
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast (show 0 < S.N by omega)
  have hge : ∀ ν ∈ L, ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β ≤ E ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) (mult R))
    rw [← hE ν] at h1
    rw [hιeq, ← hφeq]
    refine le_of_mul_le_mul_left ?_ hNpos
    nlinarith
  have hE0 : ((E ν₀ : ℤ) : ℝ) = ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β := by
    have h1 := congrArg (HMul.hMul (mult R : ℝ)) heq
    rw [← hE ν₀] at h1
    rw [hιeq, ← hφeq]
    refine mul_left_cancel₀ hNpos.ne' ?_
    nlinarith
  have hEnn : 0 ≤ E ν₀ := by
    have : (0 : ℝ) ≤ (E ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(E ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show GlobalTheory.Poinc.OrdGe M T ξ (∏ c, e c ^ ((mult R : ℤ) * j.1 c)) _
    have hle' : E ν₀ ≤ E j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, E j.1 = ((E ν₀).toNat : ℤ) + d := ⟨(E j.1 - E ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ c, w c ^ ((mult R : ℤ) * j.1 c) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show GlobalTheory.Poinc.OrdEq M T ξ (∏ c, e c ^ ((mult R : ℤ) * ν₀ c)) _
    refine ⟨∏ c, w c ^ ((mult R : ℤ) * ν₀ c), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem point_and_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  have L1 := _root_.GlobalTheory.MumCmp.exists_twist_of_samePol
  have L2 := _root_.GlobalTheory.MumCmp.isTwist_of_translate
  have L3 := _root_.GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist
  intro R _ _ _ hB D₀ D A G _ _ hG U hS
  obtain ⟨g, hz, htw⟩ := L1 R hB D₀ D hS
  refine ⟨g, hz, fun a ha hlev A₂ D₂ U₂ hL => ?_⟩
  have h2 := L2 R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨h3⟩ := L3 R hB D₀ D₂ D g htw h2
  obtain ⟨s₀, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₀
  obtain ⟨s₂, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₂
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D₀, D₂,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, inferInstance, ⟨s₀⟩, ⟨s₂⟩, ⟨h3⟩⟩

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLatticeStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_integral_completedHomLattice : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  first | exact @GlobalTheory.CosetOrth.LatInt.exists_hatPt_of_mem_latO | exact GlobalTheory.CosetOrth.LatInt.exists_hatPt_of_mem_latO | (intros; apply GlobalTheory.CosetOrth.LatInt.exists_hatPt_of_mem_latO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D hX P hA e x hg
  obtain ⟨hx, hind, hfin⟩ := _root_.GlobalTheory.HSAmp.gens_quot_trBasis k X p D hX P hA e x hg
  obtain ⟨hK, hι⟩ := _root_.GlobalTheory.isArithVar_charZero_functionField_and_injective k X p D hX
  haveI := hX.isDomain
  haveI := hX.finite
  haveI : CharZero k := ⟨fun a b h => Nat.cast_injective (R := X.functionField) (by
    have := congrArg (GlobalTheory.toFunctionField p) h
    simpa only [map_natCast] using this)⟩
  obtain ⟨hP, -, -⟩ := _root_.GlobalTheory.PSpaceDeg.main k D
  haveI : IsIntegral (PSpace k D) := hP.isIntegral
  obtain ⟨hdeg, hev⟩ := GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order k X.functionField (GlobalTheory.toFunctionField p) D x hι hind
  obtain ⟨π, hπ, hc, hiso⟩ := _root_.GlobalTheory.HSAmp.GenMap.toProj_gens k X p D hX P e x hg (hx 0)
  have hgen := _root_.GlobalTheory.GenericImage.map_genericPoint_eq k X p D π hπ x (hx 0) hc hev
  have hr := _root_.GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients k X p D π hπ x (hx 0) hc hgen
  refine ⟨inferInstance, π, hπ, hgen, ?_, ?_, hiso⟩
  · rw [hr]
    intro h0
    haveI := hfin
    have : 0 < Module.finrank (ratF x) X.functionField := Module.finrank_pos
    rw [hdeg, h0, zero_mul] at this
    exact lt_irrefl _ this
  · rw [hr, hdeg]

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPureTensorSumDatumRouteThroughSmallVertexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pureTensorSum_datum_routeThroughSmallVertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧ φ₀ ∈ GlobalTheory.WeilM.SB _ ∧ φ₀ ≠ 0 ∧
        ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin (G.V (.grid i j)).rank → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → D.host.E))
          (θ : 𝓞 D.host.E), L₁.IsLattice D.host.E ∧ L₂.IsLattice D.host.E ∧
          (∀ z : Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) z →
            (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁ ↔
              ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
                Bs.ψ (symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
                  (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) z γ) = 1)) ∧
          (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧ (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
              (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
                (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) := by
  first | exact @GlobalTheory.SmallDatumPure.exists_datum_pure_selfdual | exact GlobalTheory.SmallDatumPure.exists_datum_pure_selfdual | (intros; apply GlobalTheory.SmallDatumPure.exists_datum_pure_selfdual <;> assumption)
end

