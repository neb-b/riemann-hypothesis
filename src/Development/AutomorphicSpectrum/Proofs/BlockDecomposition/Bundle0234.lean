module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0228
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneNotMemFilOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0231
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftUnique
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartBc

section Ring
variable {R R' D : Type} [CommRing R] [CommRing R'] [CommRing D] [Algebra R R'] [Algebra R D]

theorem left_right (r : R) : (algebraMap R R' r) ⊗ₜ[R] (1 : D) = (1 : R') ⊗ₜ[R] (algebraMap R D r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem dp_right {I : Ideal R} {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {J : Ideal D}
    (δ : DividedPowers J)
    (δ' : DividedPowers (I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)))
    (hJ : J = I.map (algebraMap R D)) (hδ : IsDPMorphism γ δ (algebraMap R D))
    (hδ' : IsDPMorphism γ' δ' (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D))
    (hσ : IsDPMorphism γ γ' (algebraMap R R')) :
    IsDPMorphism δ δ' (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom := by
  have key : ∀ r : R, (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom (algebraMap R D r) =
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) (algebraMap R R' r) := fun r =>
    (left_right r).symm
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R D '' I) (by rw [hJ]; rfl) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [key]
    exact Ideal.mem_map_of_mem _ (hσ.1 (Ideal.mem_map_of_mem _ ha))
  · rintro n _ ⟨a, ha, rfl⟩
    rw [hδ.2 a ha, key, key, hδ'.2 _ (hσ.1 (Ideal.mem_map_of_mem _ ha)), hσ.2 a ha]

theorem lift_unique {I' : Ideal R'} {J : Ideal D} {B : Type} [CommRing B]
    (hle : J ≤ (I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)).comap
      (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom)
    (a : R' ⧸ I' →+* B) (b : D ⧸ J →+* B)
    (hab : ∀ r, a (Ideal.Quotient.mk I' (algebraMap R R' r)) = b (Ideal.Quotient.mk J (algebraMap R D r))) :
    ∃! φ : (R' ⊗[R] D) ⧸ I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) →+* B,
      φ.comp (Ideal.quotientMap _ (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)
        Ideal.le_comap_map) = a ∧
      φ.comp (Ideal.quotientMap _ (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom hle) = b := by
  letI : Algebra R B := ((a.comp (Ideal.Quotient.mk I')).comp (algebraMap R R')).toAlgebra
  let f1 : R' →ₐ[R] B := { a.comp (Ideal.Quotient.mk I') with commutes' := fun _ => rfl }
  let f2 : D →ₐ[R] B := { b.comp (Ideal.Quotient.mk J) with commutes' := fun r => (hab r).symm }
  let Φ : R' ⊗[R] D →ₐ[R] B := Algebra.TensorProduct.productMap f1 f2
  have hΦ : ∀ r x, Φ (r ⊗ₜ[R] x) = a (Ideal.Quotient.mk I' r) * b (Ideal.Quotient.mk J x) := fun r x => by
    simp only [Φ, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  have hker : I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) ≤ RingHom.ker Φ.toRingHom := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Φ (x ⊗ₜ[R] 1) = 0
    rw [hΦ, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, zero_mul]
  let φ := Ideal.Quotient.lift _ Φ.toRingHom fun z hz => hker hz
  have hφ : ∀ r x, φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x)) = a (Ideal.Quotient.mk I' r) * b (Ideal.Quotient.mk J x) :=
    fun r x => by
      rw [Ideal.Quotient.lift_mk]
      exact hΦ r x
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    change φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] 1)) = a (Ideal.Quotient.mk I' r)
    rw [hφ, map_one, map_one, mul_one]
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    change φ (Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] x)) = b (Ideal.Quotient.mk J x)
    rw [hφ, map_one, map_one, one_mul]
  · rintro φ₂ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_)
    refine TensorProduct.inductionOn w (fun r x => ?_) (fun u v hu hv => ?_)
    · have t : r ⊗ₜ[R] x = (r ⊗ₜ[R] (1 : D)) * ((1 : R') ⊗ₜ[R] x) := by simp
      have e1 := RingHom.congr_fun h1 (Ideal.Quotient.mk I' r)
      have e2 := RingHom.congr_fun h2 (Ideal.Quotient.mk J x)
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[R] 1)) = _ at e1
      change φ₂ (Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] x)) = _ at e2
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x)) = φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x))
      rw [hφ, t, map_mul, map_mul, e1, e2]
    · simp only [RingHom.comp_apply, map_add (f := _)] at hu hv ⊢
      rw [hu, hv]

end Ring

theorem chart_bc : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O)
    (hnil : p = 0 → IsNilpotent I') {V : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d),
    letI := σ.toAlgebra
    letI := c.D.i.toAlgebra
    ∃ (c' : Chart γ' p q κ' V d) (e : c.D ⟶ (m.mor p).functor.obj c'.D), (∀ i, e.φ (c.t i) = c'.t i) ∧
      (FlatT c.D → FlatT c'.D) ∧
      ∃ f : R' ⊗[R] c.D.B ≃+* c'.D.B, (∀ r, f (r ⊗ₜ 1) = c'.D.i r) ∧ ∀ x, f (1 ⊗ₜ x) = e.φ x := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m hu hg hnil V d c
  letI a1 : Algebra R R' := σ.toAlgebra
  letI a2 : Algebra R c.D.B := c.D.i.toAlgebra
  let iL : R' →+* R' ⊗[R] c.D.B := Algebra.TensorProduct.includeLeftRingHom
  let iR : c.D.B →+* R' ⊗[R] c.D.B := (Algebra.TensorProduct.includeRight : c.D.B →ₐ[R] R' ⊗[R] c.D.B).toRingHom
  have hcomm : ∀ r, iR (c.D.i r) = iL (σ r) := fun r => (left_right (R := R) (R' := R') (D := c.D.B) r).symm
  have hEt : (MvPolynomial.eval₂Hom iL (fun i => (1 : R') ⊗ₜ[R] c.t i) :
      MvPolynomial (Fin d) R' →+* R' ⊗[R] c.D.B).Etale :=
    GlobalTheory.CompanionTheory.ChartAlg.etale_tensor (O := R) (R := R') (G := c.D.B) c.t c.etale
  haveI hF : Module.Flat R' (R' ⊗[R] c.D.B) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale _ hEt
  obtain ⟨δ', hδ'⟩ : ∃ δ' : DividedPowers (I'.map iL), IsDPMorphism γ' δ' iL :=
    GlobalTheory.CompanionTheory.JLiftDP.dpFlat R' (R' ⊗[R] c.D.B) I' γ'
  have hle : c.D.J ≤ (I'.map iL).comap iR := by
    rw [c.J_eq]
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    change iR (c.D.i x) ∈ I'.map iL
    rw [hcomm]
    exact Ideal.mem_map_of_mem iL (m.hI.1 (Ideal.mem_map_of_mem σ hx))
  let h : c.D.B ⧸ c.D.J →+* (R' ⊗[R] c.D.B) ⧸ I'.map iL := Ideal.quotientMap _ iR hle
  let ψ : R' ⧸ I' →+* (R' ⊗[R] c.D.B) ⧸ I'.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  let y₀ : PtOver X q κ (c.D.B ⧸ c.D.J) := c.D.y
  have hw : ∀ r, y₀.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk c.D.J (c.D.i r) := c.D.w
  have hhy : h.comp y₀.1.1 = ψ.comp m.bar := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    change h (y₀.1.1 (Ideal.Quotient.mk I r)) = Ideal.Quotient.mk _ (iL (σ r))
    rw [hw, ← hcomm]
    rfl
  have hκ' : m.bar.comp κ = κ' := by
    have := m.bar_κ
    rw [hg, RingHom.comp_id] at this
    exact this
  let y' : PtOver X q κ' ((R' ⊗[R] c.D.B) ⧸ I'.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom h) ≫ pt c.D), by
      change (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) ≫ q = _
      have e0 : pt c.D ≫ q = Spec.map (CommRingCat.ofHom (y₀.1.1.comp κ)) := y₀.2
      rw [Category.assoc, e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hhy,
        RingHom.comp_assoc, hκ']⟩
  let D' : Thick (nlFun γ' p X q κ') := mkT (R' ⊗[R] c.D.B) iL (I'.map iL) δ'
    ⟨fun hp => by
      have h1 : IsNilpotent (p : c.D.B) := c.D.adm.1 hp
      have h2 := h1.map iR
      rwa [map_natCast] at h2,
     fun hp => by
      obtain ⟨n, hn⟩ := hnil hp
      exact ⟨n, by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot⟩⟩ hδ' y' (fun r => rfl)
  have hin : InU V D' := fun x _ => c.inV (show Spec.map (CommRingCat.ofHom h) x ∈ (⊤ : (Spec (CommRingCat.of (c.D.B ⧸ c.D.J))).Opens) from trivial)
  let c' : Chart γ' p q κ' V d :=
    { D := D'
      t := fun k => (1 : R') ⊗ₜ[R] c.t k
      etale := hEt
      J_eq := rfl
      inV := hin
      rep := fun B z hz => by
        let y0 : PtOver X q κ B := ⟨(z.1.1.comp m.bar, z.1.2), by
          rw [z.2, RingHom.comp_assoc, hκ']⟩
        obtain ⟨φ, hφ, hun⟩ := c.rep B y0 hz
        have hφ1 : φ.comp y₀.1.1 = z.1.1.comp m.bar := congrArg (fun w : PtOver X q κ B => w.1.1) hφ
        have hφ2 : Spec.map (CommRingCat.ofHom φ) ≫ pt c.D = z.1.2 :=
          congrArg (fun w : PtOver X q κ B => w.1.2) hφ
        have hab : ∀ r, z.1.1 (Ideal.Quotient.mk I' (algebraMap R R' r)) =
            φ (Ideal.Quotient.mk c.D.J (algebraMap R c.D.B r)) := fun r => by
          have e1 := RingHom.congr_fun hφ1 (Ideal.Quotient.mk I r)
          change φ (y₀.1.1 (Ideal.Quotient.mk I r)) = _ at e1
          rw [hw] at e1
          exact e1.symm
        obtain ⟨φ', ⟨h1, h2⟩, hu'⟩ := lift_unique (R := R) (R' := R') (D := c.D.B) hle z.1.1 φ hab
        refine ⟨φ', ?_, fun φ₂ hφ₂ => hu' φ₂ ?_⟩
        · refine Subtype.ext (Prod.ext h1 ?_)
          change Spec.map (CommRingCat.ofHom φ') ≫ (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) = z.1.2
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          have e2 : φ'.comp h = φ := h2
          rw [e2, hφ2]
        · have ha : φ₂.comp ψ = z.1.1 := congrArg (fun w : PtOver X q κ' B => w.1.1) hφ₂
          have hb : Spec.map (CommRingCat.ofHom φ₂) ≫ (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) = z.1.2 :=
            congrArg (fun w : PtOver X q κ' B => w.1.2) hφ₂
          refine ⟨ha, hun (φ₂.comp h) (Subtype.ext (Prod.ext ?_ ?_))⟩
          · change (φ₂.comp h).comp y₀.1.1 = z.1.1.comp m.bar
            rw [RingHom.comp_assoc, hhy, ← RingHom.comp_assoc, ha]
          · change Spec.map (CommRingCat.ofHom (φ₂.comp h)) ≫ pt c.D = z.1.2
            rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
            exact hb }
  let e : c.D ⟶ (m.mor p).functor.obj c'.D :=
    mkH (T' := (m.mor p).functor.obj c'.D) iR hcomm
      (dp_right (R := R) (R' := R') (D := c.D.B) c.D.δ δ' c.J_eq c.D.compat hδ' m.hI) hle
      (Subtype.ext (Prod.ext hhy (by
        change Spec.map (CommRingCat.ofHom h) ≫ pt c.D = (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) ≫ m.u
        rw [hu, Category.comp_id])))
  exact ⟨c', e, fun _ => rfl, fun _ => RingHom.flat_algebraMap_iff.2 hF, RingEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.ChartBc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSix
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem exists_inv_fil (a : ℤ) (x : Formalism.Per6.BdR l) (h1 : x ∈ Formalism.Per6.FilD l a) (h2 : x ∉ Formalism.Per6.FilD l (a + 1)) :
    ∃ y ∈ Formalism.Per6.FilD l (-a), x * y = 1 := by
  have hϖ := IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l
  have hne := IsPerfectoidField.algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ
  obtain ⟨b, rfl⟩ := (IsPerfectoidField.mem_fil_iff hϖ).1 h1
  have hb : IsUnit b := by
    by_contra hb
    have hm : b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hb
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    refine h2 ((IsPerfectoidField.mem_fil_iff hϖ).2 ⟨c, ?_⟩)
    rw [map_mul, zpow_add₀ hne, zpow_one, mul_assoc]
  obtain ⟨u, rfl⟩ := hb
  refine ⟨_, (IsPerfectoidField.mem_fil_iff hϖ).2 ⟨((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l), rfl⟩, ?_⟩
  have h3 : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) *
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h4 := mul_inv_cancel₀ (zpow_ne_zero a hne)
  rw [zpow_neg]
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) = A at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = A' at *
  generalize (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a)⁻¹ = C at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a = D at *
  linear_combination (A * A') * h4 + h3

theorem exists_gal (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL)
    (σ σ' : LL →ₐ[ℚ_[l]] Om l) (h : σ.comp τ = K.1.val) (h' : σ'.comp τ = K.1.val) :
    ∃ g : ↥(GK K), ∀ x, (g : GQ l) (σ x) = σ' x := by
  letI : Algebra LL (Om l) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL (Om l) := .of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Normal ℚ_[l] (Om l) := IsAlgClosure.normal ℚ_[l] (Om l)
  let g₀ : Om l →ₐ[ℚ_[l]] Om l := σ'.liftNormal (Om l)
  have hg₀ : ∀ x, g₀ (σ x) = σ' x := fun x => AlgHom.liftNormal_commutes σ' (Om l) x
  let g : GQ l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  refine ⟨⟨g, ?_⟩, hg₀⟩
  rw [Formalism.BasicNotions.Loc.GK, IntermediateField.mem_fixingSubgroup_iff]
  intro c hc
  have h1 : σ (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h ⟨c, hc⟩
  have h2 : σ' (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h' ⟨c, hc⟩
  change g₀ c = c
  rw [← h1, hg₀, h1, h2]

section

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem repE_toGL1 (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw)) (v : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g v = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • v := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem card_emb_le (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1) [Fintype (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)] :
    Fintype.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥Bw.Kw.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Om l)]
  exact Fintype.card_congr
    { toFun := fun τ => LL'.1.val.comp τ
      invFun := fun τ => τ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split τ x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end

end GlobalTheory.CompanionTheory.DeRhamChar

open GlobalTheory.CompanionTheory.DeRhamChar Module GlobalTheory.Cmp.JumpDict GroundTheory.PAdicHodge in
theorem GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(ReciprocityTheory.Gal.Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A _ O _ _ _ Bw _ LL' hLL ψ J hJ
  obtain ⟨T⟩ := hT
  haveI : IsDomain P.R.BdR := T.eD.toMulEquiv.isDomain (Formalism.Per6.BdR l)
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hOm : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD Bw.Kw).Fil 0 := fun x => by
    obtain ⟨y, hy, -⟩ := T.om x
    rw [T.fil, hy]
    exact (IsPerfectoidField.mem_fil_iff (IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l)).2
      ⟨y, by simp⟩
  have hval : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD Bw.Kw).Fil a → x ∉ (P.PD Bw.Kw).Fil (a + 1) →
      ∃ y ∈ (P.PD Bw.Kw).Fil (-a), x * y = 1 := fun a x h1 h2 => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_fil a (T.eD x) ((T.fil _ _ _).1 h1) (fun h => h2 ((T.fil _ _ _).2 h))
    refine ⟨T.eD.symm y, (T.fil _ _ _).2 (by simpa using hy), T.eD.injective ?_⟩
    simpa using hxy
  have hmult : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) a,
      multV (P.PD Bw.Kw) (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) τ a = if a = -J τ then 1 else 0 :=
    fun τ a => multV_inv (P.PD Bw.Kw) (GK Bw.Kw).subtype Bw.Kw.1.val (fun _ => rfl)
      (fun g x => by rw [P.PD_actdR]; exact P.actQdR_Om _ x)
      (fun g c => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 c c.2) hOm hval
      (χ := ψ.comp Bw.e.symm.toMonoidHom) (χ' := ψ⁻¹.comp Bw.e.symm.toMonoidHom)
      (fun g v => repE_toGL1 Bw LL' ψ g v) (fun g v => repE_toGL1 Bw LL' ψ⁻¹ g v)
      (fun g => by simp) τ
      (fun σ σ' h h' => exists_gal Bw.Kw τ σ σ' h h') (J τ) (fun a => hJ.2 τ a) a
  refine ⟨?_, fun τ a => hmult τ a⟩
  have := finrank_ddR_of_one_jump (P.PD Bw.Kw) (card_emb_le Bw LL' hLL)
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) (fun τ => ⟨-J τ, hmult τ⟩)
  simpa [LocBridge.IsdRE] using this
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_tied : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ₁ ψ₂ : ↥(ReciprocityTheory.Gal.Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J₁ J₂ : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₁ J₁ → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ₂ J₂ →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' (ψ₁ * ψ₂) (J₁ + J₂) := by
  first | exact @GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul | exact GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul | (intros; apply GlobalTheory.CompanionTheory.HLCMul.isdRJ_mul <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedObjPdPow
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem exists_lift {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (l : List (ℕ × B')) (hl : ∀ q ∈ l, q.2 ∈ J') :
    ∃ l' : List (ℕ × B), (∀ q ∈ l', q.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      (l.map fun q => δ'.dpow q.1 q.2).prod = f (l'.map fun q => δ.dpow q.1 q.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons q l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have hq := hl q List.mem_cons_self
    rw [hJ] at hq
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective f hs).1 hq
    refine ⟨(q.1, y) :: l', ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      exacts [hy, h1 p hp]
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3, ← e]
      rw [hf.2 y hy]

theorem dividedPowerFiltration_le_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (r : ℕ) : pdP δ' r ≤ (pdP δ r).map f := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  obtain ⟨l', h1, h2, h3⟩ := exists_lift hf hJ hs l hl
  rw [h3]
  exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨l', h1, by rwa [h2], rfl⟩)

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ}

theorem redObj_pdPow (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (r : ℕ) :
    (redObj T d h).pdPow r ≤ (T.pdPow r).map (Ideal.Quotient.mk (lnT T l n)) :=
  dividedPowerFiltration_le_map (redδ_dp T h n) rfl Ideal.Quotient.mk_surjective r
end

def toSomeP {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : ℤ) (c : b.R) (j : ℕ) :
    HM Q none c j →ₗ[b.R] HM Q (some r) c j :=
  (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI Q none c) (b' := stdI Q (some r) c)
    (fun _ => le_rfl) (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).pull j

end GlobalTheory.CompanionTheory.RedFil

namespace GlobalTheory.CompanionTheory.RedFil

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ)
  (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
  (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem val_zero (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (v : ((redG q s d 𝒱).obj T).B)
    (hv : v ∈ ((redG q s d 𝒱).obj T).pdPow r) :
    (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).τ T
      ((redMor q s d 𝒱 c lam hc none).τ T v) = 0 := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (redObj_pdPow d T.obj T.property.1 r hv)
  refine Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ?_))
  change y ∈ T.obj.pdPow (r : ℤ).toNat
  simpa using hy

theorem red_kills (r j : ℕ) : ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSomeP (TS γ q l s 𝒱) (r : ℤ) ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 y
  let S := B.pdS (nlFun δ l X q κ) c r
  let m := redMor q s d 𝒱 c lam hc none
  let t := sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)
  have h1 : CH.d _ j (S.inc.pullC j a) = 0 := by
    rw [S.inc.d_pullC]
    exact (congrArg _ ha).trans (map_zero _)
  have h2 : CH.d _ j (m.pullC j (S.inc.pullC j a)) = 0 := by
    rw [m.d_pullC, h1, map_zero]
  have h3 : CH.d _ j (t.pullC j (m.pullC j (S.inc.pullC j a))) = 0 := by
    rw [t.d_pullC, h2, map_zero]
  have e1 : S.inc.pull j ((CH.cx _).cls a ha) = (CH.cx _).cls (S.inc.pullC j a) h1 :=
    CrystallineSemistableComparison.P.mapH_cls S.inc.hom j a ha h1
  have e2 : m.pull j ((CH.cx _).cls (S.inc.pullC j a) h1) = (CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2 :=
    CrystallineSemistableComparison.P.mapH_cls m.hom j _ h1 h2
  have e3 : t.pull j ((CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2) =
      (CH.cx _).cls (t.pullC j (m.pullC j (S.inc.pullC j a))) h3 :=
    CrystallineSemistableComparison.P.mapH_cls t.hom j _ h2 h3
  have e4 : t.pullC j (m.pullC j (S.inc.pullC j a)) = 0 := by
    funext σ
    exact val_zero d q s 𝒱 c lam hc r _ _ (a (((σ ⋙ t.G) ⋙ m.G) ⋙ S.inc.G)).2
  change t.pull j (m.pull j (S.inc.pull j _)) = 0
  rw [e1, e2, e3]
  exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ h3).2 (by rw [e4]; exact Submodule.zero_mem _)
end

end GlobalTheory.CompanionTheory.RedFil
end
end

