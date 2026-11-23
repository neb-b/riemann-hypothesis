module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0012
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0005
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Isotypic₂
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0010
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0009
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.FixedDvd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (Polynomial.X - 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)

private theorem UpperTheory.V.Z.Win.T2.char_of_dvd {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ) (hM : 1 ≤ M) (x z : WD h)
    (hx : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      x.charPol (ineIncl h s) = (Polynomial.X - 1) ^ n)
    (hz : IsIrrWD z) (hd : ∀ σ, z.charPol σ ∣ x.charPol σ) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h2 := hd (ineIncl h s)
    rw [hx s hs, WD.charPol_mk] at h2
    exact UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩

private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2

private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.FixedUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩

private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.SegmentV
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.T2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

private theorem segmentV {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    (H : LawsV a ha ε rc) {Δ : Segment (w.adicCompletion E)} {x : IrrGL (k := w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) :
    rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) :=
  (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)

end UpperTheory.V.Z.Win.T2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.TypeData
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ UpperTheory.NonzeroTypeTheory UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.T2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

private theorem good_of_sph (x : IrrGL (k := w.adicCompletion E)) (hx : IsSpherical x.rep) : Good x := by
  obtain ⟨s, hs, h1⟩ := GlobalTheory.SphSupport.toral_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ x hx
  refine ⟨s, hs, fun y hy => Or.inl ?_⟩
  obtain ⟨χ, -, hχ, rfl⟩ := h1 y hy
  rfl

private theorem sph_of {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hσ : IsSpherical σ) : IsSpherical (IrrGL.of σ hs hi).rep :=
  SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hσ

private theorem sphOfUnrV (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) (d : ℕ) (v : WD h) (hv : v.unr) (hd : v.lpDim = d) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
      (hs : IsSmooth σ) (hi : σ.IsIrreducible), IsSpherical σ ∧ rc (IrrGL.of σ hs hi) = v := by
  subst hd
  obtain ⟨α, hα⟩ := GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h v hv
  obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
  have φ := equivRep π
  have hπ' : HasSatake (GlobalTheory.LocLanglands.cls π).rep α := ⟨IrrRep.irr _, SphericalUnramified.isSpherical_of_equiv φ hπ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.smooth, π.irr, hπ.2.1, ?_⟩
  exact (H.sat (GlobalTheory.LocLanglands.cls π) α hπ').trans hα.symm

private theorem prodRcV (L : UpperTheory.V.Z.Win.LawsV a ha ε rc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b))
      (hs : ∀ b, IsSmooth (σ b)) (hi : ∀ b, (σ b).IsIrreducible)
      (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible),
      rc (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI) =
        sumList (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b))) := by
  intro s
  induction s with
  | zero =>
    intro N d hd X _ _ σ hs hi hI
    have h0 : N = 0 := by simpa using hd.symm
    rw [List.ofFn_zero, sumList, List.foldr_nil]
    exact P_prodRc.wd_eq_lpZero ((L.dim (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI)).trans h0)
  | succ s ih =>
    intro N d hd X _ _ σ hs hi hI
    obtain rfl : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨Φ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hts : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => σ i.succ) :=
      isSmooth_parInd _ _
    have hti := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0) _ (multiProd (stdBlocks d hd) σ)
      (hs 0) (hi 0) hts hI ⟨Φ.symm⟩
    have key := L.prod (d 0) (∑ i : Fin s, d i.succ) ⟨X 0, σ 0, hs 0, hi 0⟩ ⟨_, _, hts, hti⟩
      ⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _, hI⟩ ⟨Φ.symm⟩
    refine key.trans ?_
    rw [List.ofFn_succ, sumList, List.foldr_cons]
    congr 1
    exact ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs i.succ)
      (fun i => hi i.succ) hti

private theorem good_prod (hL : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type)
    [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
    (τ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b)) (hs : ∀ b, IsSmooth (τ b))
    (hi : ∀ b, (τ b).IsIrreducible) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ) (hη : ∀ b, IsSmoothChar (η b))
    (hdet : ∀ b, HasDetVec (τ b) (η b)) (hI : (multiProd (stdBlocks d hd) τ).IsIrreducible) :
    Good (IrrGL.of (multiProd (stdBlocks d hd) τ) (isSmooth_parInd _ _) hI) := by
  choose μ hμ hcs using fun b => step_cuspSupp hL _ (d b) (X b) (τ b) (hs b) (hi b) (η b) (hη b) (hdet b)
  have hS := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel hd τ hs hi
    (fun b => hasSupport_of_isCuspSupport (hcs b)) hI
  refine ⟨_, hS.of_equiv (IrrGL.equivOf _ _ _), fun y hy => Or.inl ?_⟩
  obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
  rfl

private theorem gMainV (hLit : GlobalTheory.Mem.LiteralAutomorphy.LitLoc) (gi : ArtinInertiaProp) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    {s : ℕ} (d : Fin s → ℕ) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ) (hη : ∀ b, IsSmoothChar (η b))
    (hdist : ∀ b c, b ≠ c → ∃ t : Ine (F := E) A, η b (a (ineIncl h t)) ≠ η c (a (ineIncl h t)))
    (x : IrrGL (k := w.adicCompletion E)) (hd : ∑ b, d b = x.1) :
    ((rc x).mono0 ∧ ∀ t : Ine (F := E) A,
        (rc x).charPol (ineIncl h t) = ∏ b, (X - C ((η b (a (ineIncl h t)) : ℂˣ) : ℂ)) ^ d b) ↔
      IsTwSphProd x.rep d hd η := by
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := step_isotypic E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := step_scalarInertia E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => sphOfUnrV H (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    have hs' : ∀ b, IsSmooth (twist (σ b) (detChar (Fin (d b)) (η b))) :=
      fun b => isSmooth_twist (hs b) (hη b).detChar
    have hi' : ∀ b, (twist (σ b) (detChar (Fin (d b)) (η b))).IsIrreducible := fun b => isIrreducible_twist (hi b) _
    have hrc' : ∀ b, rc (IrrGL.of (twist (σ b) (detChar (Fin (d b)) (η b))) (hs' b) (hi' b)) =
        (rc (IrrGL.of (σ b) (hs b) (hi b))).lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := fun b => by
      rw [← IrrGL.tw_of (hχ := hη b), H.twist _ _ _ (good_of_sph _ (sph_of _ _ _ (hsph b))), H.one]
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (step_detVec _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (gi E Ω A w h a ha).1 t, ht⟩
    have hI := step_prodIrr step_cuspSupp hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi'
      η hη hdet hdistU
    have hrcP := prodRcV H s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (H.inj x _ (good_prod hLit d hd Xs _ hs' hi' η hη hdet hI) heq.symm).symm.trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      have hs' : IsSmooth (twist (σ b) (detChar (Fin (d b)) (η b)⁻¹)) := isSmooth_twist (hs b) (hη b).inv.detChar
      have hi' : (twist (σ b) (detChar (Fin (d b)) (η b)⁻¹)).IsIrreducible := isIrreducible_twist (hi b) _
      have hsp := sph_of _ hs' hi' ((step_detVec _ (d b) (Xs b) (σ b) (η b)).2 (hdet b))
      refine ⟨_, (H.sph _).1 hsp, H.dim _, ?_⟩
      rw [P_untwistRc.of_eq_tw (σ b) (hs b) (hi b) (η b) (hη b), H.twist _ _ _ (good_of_sph _ hsp), H.one]
    choose u hu hud hur using hfac
    have hl := step_sumList E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := prodRcV H s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (step_unrTwist E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (step_unrTwist E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl

end UpperTheory.V.Z.Win.T2
end
end

