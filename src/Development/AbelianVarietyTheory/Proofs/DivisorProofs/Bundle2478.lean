module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFacts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem cmp_mul (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x y : N'.A) (j : Fin r) :
    cmp T ν ν' (x * y) j = cmp T ν ν' x j * cmp T ν ν' y j := by
  haveI := T.pr_hom j
  simp only [TensTor.cmp, map_mul]
  rw [← map_mul ν.eA.symm]
  congr 1
  exact GlobalTheory.TorusDefect.mul_comp_of_pullback (jK R) (T.pr j) (jFK F) (jFK F ≫ jK R) rfl (ν'.eA x) (ν'.eA y)

theorem cmp_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (cmp T ν ν') := by
  constructor
  · intro x y h
    apply ν'.eA.injective
    refine Fan.IsLimit.hom_ext T.lim _ _ fun j => ?_
    have := congrFun h j
    simpa [TensTor.cmp] using this
  · intro f
    refine ⟨ν'.eA.symm (Fan.IsLimit.lift T.lim fun j => ν.eA (f j)), funext fun j => ?_⟩
    simp only [TensTor.cmp, MulEquiv.apply_symm_apply]
    refine (congrArg ν.eA.symm (Fan.IsLimit.fac T.lim _ j)).trans ?_
    simp

theorem chi_add (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ χ' : N'.X) (i : Fin r) :
    chi T ν ν' (χ + χ') i = chi T ν ν' χ i + chi T ν ν' χ' i := by
  simp [TensTor.chi, map_add (f := _)]

theorem chi_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (chi T ν ν') := by
  have : chi T ν ν' = ν'.eX.trans (T.xe.trans (AddEquiv.piCongrRight fun _ => ν.eX.symm)) := by
    funext χ i; rfl
  rw [this]; exact AddEquiv.bijective _

theorem cmp_c (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) (j : Fin r) :
    cmp T ν ν' (N'.c χ') j = N.c (chi T ν ν' χ' j) := by
  simp only [TensTor.cmp, TensTor.chi]
  rw [ν.eA.symm_apply_eq, ν.c_eq, ν'.c_eq, ν.eX.apply_symm_apply]
  simp only [DegPre.cF, Category.assoc, T.c_pr]

theorem wv_ne_zero (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : wv T ν ν' x ≠ 0 := by
  unfold TensTor.wv valF
  rw [dite_eq_left]
  · exact (((T.w.s _).isUnit.map _).map _).ne_zero
  · intro p _
    refine ⟨Set.mem_iInter.2 fun k => ?_, ν'.good _ trivial⟩
    exact ν.good ((ν'.eA x).left ≫ tensφ T.pr k) (show p ∈ (⊤ : (Sp F).Opens) from trivial)

end GlobalTheory.Mum.TensTor


open GlobalTheory.Mum.TensTor in
theorem GlobalTheory.Mum.TensTor.tensFacts_holds : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), TensFacts W (cmp T ν ν') (chi T ν ν') (wv T ν ν') := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν'
  exact ⟨cmp_mul T ν ν', cmp_bijective T ν ν', chi_add T ν ν', chi_bijective T ν ν', cmp_c T ν ν', wv_ne_zero T ν ν',
    _root_.GlobalTheory.Mum.TensCube.theta_tens R hB D D' W T F N N' ν ν', _root_.GlobalTheory.Mum.TensTor.tensFacts_psi R hB D D' W T F N N' ν ν'⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThListTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalTh

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]; rw [← Spec.map_comp]; rfl

theorem sp_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp only [spMap]; exact Spec.map_id _

theorem sp_cancel {F K : Type} [Field F] [Field K] (i : F →+* K) {X : Scheme.{0}} (a b : Sp F ⟶ X)
    (h : spMap i ≫ a = spMap i ≫ b) : a = b := by
  haveI : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective a
  obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  obtain ⟨rfl, e⟩ := GlobalTheory.SS.residue_embedding_unique _ _ h
  have : φ = ψ := by
    ext c
    have := congrArg (fun g => g.hom c) e
    simp at this
    exact i.injective this
  rw [this]

theorem exists_descend {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (H : Subgroup (K ≃ₐ[Ω] K)) {X : Scheme.{0}}
    (p : Sp K ⟶ X) (hp : ∀ τ ∈ H, spMap (τ : K →+* K) ≫ p = p) :
    ∃ q : Sp (IntermediateField.fixedField H) ⟶ X, spMap (algebraMap (IntermediateField.fixedField H) K) ≫ q = p := by
  obtain ⟨E, h₁, h₂, -⟩ := GlobalTheory.SS.exists_fieldOfValues X K p
  refine (h₂ _ (algebraMap (IntermediateField.fixedField H) K)).1 fun c hc => ?_
  have hfix : c ∈ IntermediateField.fixedField H := (IntermediateField.mem_fixedField_iff _ _).2 fun τ hτ =>
    (h₁ (τ : K →+* K) (RingHom.id K)).1 (by rw [sp_id, Category.id_comp]; exact hp τ hτ) c hc
  exact ⟨⟨c, hfix⟩, rfl⟩

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_transport (m : ℕ) {K : Type} [Field K] {T : Over S} (θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T))
    {y y' : Sp K ⟶ S} (hy : y = y') (h : Over.mk y ⟶ T) (h' : Over.mk y' ⟶ T) (hh : h.left = h'.left)
    {N : ℕ} (pt : Fin N → (Over.mk y ⟶ G)) (c : Fin N → K)
    (H : ThList G L ρ m y (VVRank.pullS G _ h θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), (∀ a, (pt' a).left = (pt a).left) ∧
      ThList G L ρ m y' (VVRank.pullS G _ h' θ) pt' c := by
  subst hy
  obtain rfl : h = h' := Over.OverMorphism.ext hh
  exact ⟨pt, fun _ => rfl, H⟩

theorem thList_comp (m : ℕ) {R K₁ K₂ : Type} [CommRing R] [Field K₁] [Field K₂] (i : R →+* K₁) (j : K₁ →+* K₂)
    (k : R →+* K₂) (hk : j.comp i = k) (x : Sp R ⟶ S) (θ : SecAt G L x) {N : ℕ}
    (pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)) (c : Fin N → K₂)
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap k ≫ x) ⟶ G), (∀ a, (pt' a).left = (pt a).left) ∧
      ThList G L ρ m (spMap k ≫ x) (SecAt.pull G L θ k) pt' c := by
  unfold SecAt.pull at H ⊢
  rw [GlobalTheory.ThetaRuleCompare.pullS_comp] at H
  exact thList_transport m θ (by rw [← hk, sp_comp, Category.assoc]) _ _ (by simp [← hk, sp_comp]) pt c H

end

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_exh {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {y : Sp K ⟶ S} {θ : SecAt G L y} {N : ℕ}
    {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y θ pt c) (p : Over.mk y ⟶ G)
    (hp : p ^ (m ^ 2) = 1) : ∃ a, p = pt a := by
  let u : Over.mk (spMap (RingHom.id K) ≫ y) ⟶ Over.mk y := Over.homMk (spMap (RingHom.id K)) rfl
  obtain ⟨a, ha⟩ := H.2.2 K (RingHom.id K) (u ≫ p) (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  refine ⟨a, Over.OverMorphism.ext ?_⟩
  simpa [u, sp_id] using ha

end

end GlobalTheory.UMin.GalTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantKthRootLabelledPointUpToRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaAtRoot

section
variable {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A)))

theorem val_powFrame' {T : Over S} (x : T ⟶ P.A) (e) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame P.A P.L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem isThetaConst_of_thG (hrig : rig.IsGen) {m : ℕ} {T : Over S} {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)}
    {x : T ⟶ P.A} {c : Γ(T.left, ⊤)} (H : ThG P.A P.L rig m th x c) :
    ∃ (s₁ s₂ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T),
      GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m ((m ^ 2 : ℕ) : ℤ) th s₁ ∧ SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧
      IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ s₂ ∧ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig ((m ^ 2 : ℕ) : ℤ) s₂ c := by
  obtain ⟨-, t, α, s₁, θ, hα, h₂, h₃, h₄, h₅, h₆⟩ := H
  refine ⟨s₁, t, θ, ⟨α, hα, corr_of_val P.isLB fun y J hJ => ?_, h₃⟩, h₄, h₅,
    ⟨rigT P.A P.L rig T ((m ^ 2 : ℕ) : ℤ), GlobalTheory.ThetaReal.NormMul.rigT_isGen hrig _, corr_of_val P.isLB fun _ _ _ => rfl,
      GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => by rw [Category.id_comp]; exact h₆ y J hJ⟩⟩
  refine (val_corr hJ h₂ (𝟙 _)).trans ?_
  rw [val_mul hJ, val_inv, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ,
    GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, zpow_sub_one, zpow_one]

theorem frame_pull {n : ℕ} {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x₀ e₀) :
    IsTorsFrame P rig n (u ≫ x₀) (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) := by
  obtain ⟨h₁, h₂, α, hα, hN, hc⟩ := H
  refine ⟨by rw [← MonObj.comp_pow, h₁, MonObj.comp_one], LB.isGen_pullGen _ _ _ _ h₂ _, α, hα, hN,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  have q := val_corr hJ hc u.left
  rw [val_powFrame', val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Over.w u] at q
  rw [val_powFrame', val_pull hJ, val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Category.id_comp,
    Category.id_comp, Category.id_comp, Over.comp_left]
  exact q

theorem value_pull {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    {th : LB.Sec (LPow P.A P.L 1 T₀)} {c : Γ(T₀.left, ⊤)} (H : IsValueAt P.A P.L 1 th x₀ e₀ c) :
    IsValueAt P.A P.L 1 (VVRank.pullS P.A 1 u th) (u ≫ x₀)
      (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) (u.left.appTop.hom c) := by
  refine GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => ?_
  have e : (ptSecT P.A (u ≫ x₀)) ≫ (u ▷ P.A) = u ≫ ptSecT P.A x₀ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (𝟙 _ ≫ (ptSecT P.A (u ≫ x₀)).left) ≫ (u ▷ P.A).left = u.left ≫ (ptSecT P.A x₀).left := by
    rw [Category.id_comp, ← Over.comp_left, e, Over.comp_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e', GlobalTheory.ThetaPtMove.sv_of_isValueAt H u.left y hJ, val_pull hJ, Category.id_comp]
  exact congrArg (· * _) (gs_pull (𝟙 _) u.left y ⊤ trivial c).symm

end

end GlobalTheory.ThetaAtRoot

namespace GlobalTheory


open GlobalTheory.ThetaAtRoot in
theorem thetaConst_pow_eq_at_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i b y v hy H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow
  let u : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  have hfr := frame_pull ρ.P ρ.rig u (ρ.fr_tors b)
  have ht := value_pull ρ.P u (ρ.th_val b)
  obtain ⟨s₁, s₂, U, h₁, hU, hs, h₃⟩ := isThetaConst_of_thG ρ.P ρ.rig ρ.rig_gen H
  let z : Sp K := (⊥ : PrimeSpectrum K)
  obtain ⟨ξ, hξ, e⟩ := GlobalTheory.ThetaCompare.normalised_root_stalk hL.globalFns ρ.P hk hy hfr ht _
    (Nat.cast_pow (S.r * S.N) 2) h₁ hU hs h₃ z
  have ec : u.left.appTop.hom (GlobalTheory.ZH.fn (⟨S.th b, S.th_mem b⟩ : S.R)) = GlobalTheory.ZH.fn (i ⟨S.th b, S.th_mem b⟩) :=
    (congrArg (fun q => q.hom (⟨S.th b, S.th_mem b⟩ : S.R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
  rw [ec] at e
  let iso := Scheme.ΓSpecIso (CommRingCat.of K)
  let g : K →+* (Sp K).presheaf.stalk z := ((Sp K).presheaf.germ ⊤ z trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp K) (U := ⊤) z trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ a : K, gs (𝟙 (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left) z ⊤ (GlobalTheory.ZH.fn a) = g a :=
    fun a => gs_eq _ z ⊤ trivial _
  apply hg
  rw [map_pow, map_pow, ← hgs, ← hgs, e, mul_pow, ← Units.val_pow_eq_pow_val, hξ, Units.val_one, _root_.one_mul]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueAndLinearInSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.UMin

theorem thG_smul_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K), Odd m → (m : K) ≠ 0 → PolFib G L g x → SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ → ThG G L ρ m θ p (GlobalTheory.ZH.fn c) → (ThG G L ρ m θ' p (GlobalTheory.ZH.fn c') ↔ c' = a * c) := by
  intro S G _ _ L ρ hL hρ g m K _ x θ θ' p a c c' hm hmK hpol hθ H
  obtain ⟨P, φ, -, hp, w, hw⟩ := hpol
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hfn : ∀ u v : K, GlobalTheory.ZH.fn (u * v) = GlobalTheory.ZH.fn u * GlobalTheory.ZH.fn v := fun u v => map_mul _ u v
  have Ha : ThG G L ρ m θ' p (GlobalTheory.ZH.fn (a * c)) := by
    rw [hfn]; exact ThG.smul hL hθ H
  refine ⟨fun H' => ?_, fun h => h ▸ Ha⟩
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  obtain ⟨z, hz, hz'⟩ := exists_torsion_down hp τ hτ p H.1
  obtain ⟨t', ht'⟩ := exists_secRel hp τ hτ hw hL hL₁ θ'
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
    exact (IsUnit.mk0 _ (by push_cast; exact pow_ne_zero _ hmK)).map _
  have q := ThG.unique abelianSchemeLaws_all.1 P hm hun (ThG.move hp τ hτ hw hL hL₁ hr hz hz' ht' H')
    (ThG.move hp τ hτ hw hL hL₁ hr hz hz' ht' Ha)
  have q' : GlobalTheory.ZH.fn c' = GlobalTheory.ZH.fn (a * c) := by simpa [τ] using q
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective q'

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphism
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaConj

def conjHom {R : Type} [CommRing R] [IsDomain R] (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact σ.commutes a)

end GlobalTheory.ThetaConj


open GlobalTheory.ThetaConj GlobalTheory.ThetaCoord in
theorem GlobalTheory.isThetaPt_conj : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  intro R _ _ A k σ I x x' v hx H
  have hs : Subsingleton (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Kb R)))
  have hn : Nonempty (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Kb R)))
  let e : Kb R ≃ₐ[FractionRing R] Kb R :=
    AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hi : conjHom σ ≫ conjHom e.symm.toAlgHom = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    ext a
    exact e.apply_symm_apply a
  have Q := isThetaPtOver_pull A (isThetaPtOver_of_subsingleton A H) _ _ hi
  have Q' : IsThetaPtOver A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
    convert Q using 2 with a a
    · exact Over.OverMorphism.ext (hx a)
    · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom))
  refine ⟨H.1, H.2.1, fun p => ⟨⊤, trivial, ?_⟩⟩
  let j : TFK (R := R) (Kb R) ⟶ overRes (T := TFK (R := R) (Kb R)) ⊤ :=
    Over.homMk (TFK (R := R) (Kb R)).left.topIso.inv (by
      change _ ≫ Scheme.Opens.ι ⊤ ≫ _ = _
      rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  exact isThetaPtOver_pull A Q' (overResι ⊤) j
    (Over.OverMorphism.ext (TFK (R := R) (Kb R)).left.topIso.hom_inv_id)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarised
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem topCoeff_finsum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem topCoeff_const_mul {n : ℕ} (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (MvPolynomial.C a * P) = a * topCoeff P := by
  simp only [topCoeff, MvPolynomial.coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem topCoeff_chernPoly_eq_mixTop : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    topCoeff (chernPoly G v n) = mixTop fun _ => curvAt G v := by
  intro n r _ _ G v
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have key := _root_.GlobalTheory.GoodTop.factorial_mul_coeff_charpolyRev_neg (curvPoly G v) n
  have h1 : (n.factorial : ℂ) * topCoeff (chernPoly G v n) =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
          (Matrix.of fun i b => curvAt G v (u i) b (p i) (p (π i))).det := by
    rw [← topCoeff_const_mul, map_natCast, chernPoly, key, topCoeff_finsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [topCoeff_finsum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ), topCoeff_const_mul]
    have hp : (∏ i, curvPoly G v (p i) (p (π i))) = ∏ i, ∑ a, ∑ b,
        MvPolynomial.C (curv G v (coordVec a) (coordVec b) (p i) (p (π i))) * MvPolynomial.X (a, b) := by
      simp [curvPoly]
    rw [hp, _root_.GlobalTheory.GoodTop.topCoeff_prod_forms, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [curvAt, mul_assoc]
  rw [mixTop, ← h1, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end GlobalTheory.GoodTop
end
end

