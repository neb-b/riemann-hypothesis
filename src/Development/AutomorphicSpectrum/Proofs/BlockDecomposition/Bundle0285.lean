module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMPull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnOfFderivFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgSubOfPer
section
open GlobalTheory.CuspGeneric

namespace GlobalTheory.CompanionTheory.CuspGeneric

theorem avg_sub_of_per : ∀ {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (Γ : AddSubgroup G), IsCoLat Γ → ∀ (Φ Φ' : G → ℂ), Per Γ Φ → Per Γ Φ' →
    avg Γ (fun x => Φ x - Φ' x) = avg Γ Φ - avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  have hn : Per Γ (fun x => (-1 : ℂ) * Φ' x) :=
    ⟨continuous_const.mul h'.1, fun γ hγ x => by simp only [h'.2 γ hγ x]⟩
  have key := avg_add_of_per G Γ hΓ Φ (fun x => (-1 : ℂ) * Φ' x) h hn
  have e : (fun x => Φ x - Φ' x) = fun x => Φ x + (-1 : ℂ) * Φ' x := by
    funext x; ring
  rw [e, key, avg_const_mul]
  ring

end GlobalTheory.CompanionTheory.CuspGeneric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonal
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CellDiag

def evalOne {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) :
    smoothPart (ind H σ) →ₗ[ℂ] W :=
  (LinearMap.proj (1 : G)).comp ((indSpace H σ).subtype.comp (smoothPart (ind H σ)).subtype)

theorem evalOne_injective {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H : Subgroup G) (hH : H = ⊤) (σ : Representation ℂ H W) :
    Function.Injective (evalOne H σ) := by
  subst hH
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have h0 : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1 = 0 := hv
  have hmem : ∀ (h : (⊤ : Subgroup G)) (x : G),
      (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 (↑h * x) =
        σ h ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x) :=
    (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).2
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have key : (v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 x =
      σ ⟨x, Subgroup.mem_top x⟩ ((v : GlobalTheory.PRep.indSpace (⊤ : Subgroup G) σ).1 1) := by
    have := hmem ⟨x, Subgroup.mem_top x⟩ 1
    rwa [mul_one] at this
  rw [key, h0, map_zero]
  first
  | rfl
  | simp

theorem dichotomy {V X T : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup T] [Module ℂ T] [Module.Finite ℂ X] (hX : Module.finrank ℂ X ≤ 1)
    (hT : Module.finrank ℂ T = 1) (ι : V →ₗ[ℂ] X) (hι : Function.Injective ι)
    (φ ψ : V →ₗ[ℂ] T) : φ = 0 ∨ ∃ c : ℂ, ψ = c • φ := by
  classical
  by_cases hφ : φ = 0
  · exact Or.inl hφ
  right
  haveI : Module.Finite ℂ V := Module.Finite.of_injective ι hι
  have hV : Module.finrank ℂ V ≤ 1 := (LinearMap.finrank_le_finrank_of_injective hι).trans hX
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hφ (LinearMap.ext hne)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero φ)
  haveI : Nontrivial V := ⟨⟨v, 0, hv0⟩⟩
  have hV1 : Module.finrank ℂ V = 1 := le_antisymm hV Module.finrank_pos
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (φ v) hv).mp hT (ψ v)
  refine ⟨c, LinearMap.ext fun w => ?_⟩
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).mp hV1 w
  first
  | (rw [← ht, map_smul, map_smul, LinearMap.smul_apply, ← hc]; done)
  | (rw [← ht, ← hc]; simp [smul_comm])
  | (subst ht; simp [← hc, smul_smul, mul_comm])

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sizeMatrix_true_false {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0) :
    B.1 true false = 0 := by
  have hr := B.2.1 false
  have hc := B.2.2 false
  first
  | (rw [Fintype.sum_bool] at hr hc; omega)
  | (simp only [Fintype.sum_bool] at hr hc; omega)

theorem relParab_eq_top {a b : ℕ}
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (h : B.1 false true = 0)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j) :
    relParab k (c := fun j i => Fin (B.1 i j)) g = ⊤ := by
  have h' := GlobalTheory.CompanionTheory.CellDiag.sizeMatrix_true_false B h
  rw [eq_top_iff]
  intro x _
  rw [GlobalTheory.SmGL.relParab, Subgroup.mem_pi]
  intro j _
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro p q i i' hqp
  rw [Bool.lt_iff] at hqp
  obtain ⟨rfl, rfl⟩ := hqp
  exfalso
  cases j
  · have := i.isLt
    omega
  · have := i'.isLt
    omega

theorem diag_cell_at_most_one_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ B f g h φ ψ
  have hT : Module.finrank ℂ (ℂ ⊗[ℂ] ℂ) = 1 := by
    first
    | rw [Module.finrank_tensorProduct, Module.finrank_self]
    | simp [Module.finrank_tensorProduct]
    | simp
  refine GlobalTheory.CompanionTheory.CellDiag.dichotomy ?_ hT
    (GlobalTheory.CompanionTheory.CellDiag.evalOne _ _)
    (GlobalTheory.CompanionTheory.CellDiag.evalOne_injective _ (GlobalTheory.CompanionTheory.CellDiag.relParab_eq_top (k := k) B h g) _)
    φ.toLinearMap ψ.toLinearMap
  first
  | exact (Submodule.finrank_quotient_le _).trans hT.le
  | exact (Submodule.finrank_quotient_le _).trans (le_of_eq hT)
  | (refine (Submodule.finrank_quotient_le _).trans ?_; simp)

end GlobalTheory.CompanionTheory.CellDiag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLiftTensorCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

noncomputable section
namespace GlobalTheory.CompanionTheory.DisoHm
section Cmp
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_base {W : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU W T) (a : O) (r : R)
    (hr : κ a = Ideal.Quotient.mk I r) : ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i r) := by
  have e := evalAt_base q κ (show PtOver X q κ (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q κ (T.B ⧸ T.J) from T.y).2 h a
  refine e.trans ?_
  rw [hr]
  exact T.w r

theorem quot_eq_id {W : X.Opens} {d : ℕ} (c : Chart γ p q κ W d) (hW : IsAffineOpen W)
    (θ : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J)
    (h1 : ∀ r, θ (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r))
    (h2 : ∀ f, θ (ev c.D c.inV f) = ev c.D c.inV f) : θ = RingHom.id _ := by
  have key : ∀ θ' : c.D.B ⧸ c.D.J →+* c.D.B ⧸ c.D.J,
      (∀ r, θ' (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (c.D.i r)) →
      (∀ f, θ' (ev c.D c.inV f) = ev c.D c.inV f) →
      (ptFun X q κ).map (CommRingCat.ofHom θ') c.D.y = c.D.y := by
    intro θ' a b
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have w := c.D.w r
      change θ' ((show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)) =
        (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r)
      have w' : (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (c.D.i r) := w
      rw [w']
      exact a r
    · change Spec.map (CommRingCat.ofHom θ') ≫ pt c.D = pt c.D
      have e : Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec = pt c.D :=
        GlobalTheory.CompanionTheory.ChartAlg.eq_specMap hW (pt c.D) c.inV
      have e2 : θ'.comp (ev c.D c.inV) = ev c.D c.inV := RingHom.ext b
      calc Spec.map (CommRingCat.ofHom θ') ≫ pt c.D
          = Spec.map (CommRingCat.ofHom θ') ≫ Spec.map (CommRingCat.ofHom (ev c.D c.inV)) ≫ hW.fromSpec := by rw [e]
        _ = Spec.map (CommRingCat.ofHom (θ'.comp (ev c.D c.inV))) ≫ hW.fromSpec := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = pt c.D := by rw [e2, e]
  obtain ⟨g₀, -, hu⟩ := c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV
  exact (hu _ (key θ h1 h2)).trans (hu _ (key _ (fun _ => rfl) (fun _ => rfl))).symm

end Cmp

theorem cmp_bij : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  intro l _ O _ X q h W d c m cL hcL cO
  letI := (strV q W).toAlgebra
  intro e he het hev hT σ hσ
  let E : Γ(X, W) ≃+* cO.D.B := (Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv.trans e
  have hE : ∀ f, E f = e (1 ⊗ₜ f) := fun f => rfl
  have hEs : ∀ a, E (strV q W a) = cO.D.i a := fun a => by
    rw [hE, ← he]
    congr 1
    change (1 : O) ⊗ₜ[O] (algebraMap O Γ(X, W) a) = a ⊗ₜ 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hEt : ∀ i, E (c.t i) = cO.t i := het
  have hevE : ∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (E f) := hev
  let ψ : MvPolynomial (Fin d) O →+* cO.D.B := MvPolynomial.eval₂Hom cO.D.i cO.t
  have hψ : ψ.Etale := cO.etale
  let g : cO.D.B →+* cL.D.B ⧸ cL.D.J := (ev cL.D cL.inV).comp (E.symm : cO.D.B →+* Γ(X, W))
  let f₁ : MvPolynomial (Fin d) O →+* cL.D.B :=
    MvPolynomial.eval₂Hom (cL.D.i.comp (Ideal.Quotient.mk _)) cL.t
  have hg1 : ∀ f, g (E f) = ev cL.D cL.inV f := fun f => by
    change ev cL.D cL.inV (E.symm (E f)) = _
    rw [RingEquiv.symm_apply_apply]
  have hc : g.comp ψ = (Ideal.Quotient.mk cL.D.J).comp f₁ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have e1 : ψ (MvPolynomial.C a) = E (strV q W a) := by
        rw [hEs]; simp [ψ]
      have e2 : f₁ (MvPolynomial.C a) = cL.D.i (Ideal.Quotient.mk _ a) := by simp [f₁]
      change g (ψ (MvPolynomial.C a)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.C a))
      rw [e1, e2, hg1]
      exact ev_base cL.D cL.inV a _ rfl
    · have e1 : ψ (MvPolynomial.X i) = E (c.t i) := by
        rw [hEt]; simp [ψ]
      have e2 : f₁ (MvPolynomial.X i) = cL.t i := by simp [f₁]
      change g (ψ (MvPolynomial.X i)) = Ideal.Quotient.mk cL.D.J (f₁ (MvPolynomial.X i))
      rw [e1, e2, hg1]
      exact hcL i
  obtain ⟨H, ⟨hH1, hH2⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.EtNil.etLift_of_nil cL.D.J (GlobalTheory.CompanionTheory.ChartMaps.nil_J cL.D) _ _ ψ hψ f₁ g hc
  have hHi : ∀ a, H (cO.D.i a) = cL.D.i (Ideal.Quotient.mk _ a) := fun a => by
    have := RingHom.congr_fun hH1 (MvPolynomial.C a)
    simpa [ψ, f₁] using this
  have hHt : ∀ i, H (cO.t i) = cL.t i := fun i => by
    have := RingHom.congr_fun hH1 (MvPolynomial.X i)
    simpa [ψ, f₁] using this
  have hHe : ∀ f, Ideal.Quotient.mk cL.D.J (H (E f)) = ev cL.D cL.inV f := fun f => by
    rw [← hg1, ← hH2]
    rfl
  have hk : ∀ a ∈ lm (l := l) cO.D m, H a = 0 := by
    have hle : lm (l := l) cO.D m ≤ RingHom.ker H := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change H ((l : cO.D.B) ^ m) = 0
      have e1 : (l : cO.D.B) ^ m = cO.D.i ((l : O) ^ m) := by
        rw [map_pow, map_natCast]
      rw [e1, hHi, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    exact fun a ha => hle ha
  let Hb : GB (l := l) cO.D m →+* cL.D.B := Ideal.Quotient.lift _ H hk
  have hHb : ∀ x, Hb (Ideal.Quotient.mk _ x) = H x := fun x => Ideal.Quotient.lift_mk _ H hk
  let mkG : cO.D.B →+* (GObj h cO.D m hT).B := Ideal.Quotient.mk (lm (l := l) cO.D m)
  have hV := inU_G h cO.D m hT cO.inV
  have hs : σ.φ.comp H = mkG := by
    have uniq := _root_.GlobalTheory.CompanionTheory.EtNil.etLift_of_nil (GObj h cO.D m hT).J (GlobalTheory.CompanionTheory.ChartMaps.nil_J (GObj h cO.D m hT)) _ _ ψ hψ
      (mkG.comp ψ) ((Ideal.Quotient.mk (GObj h cO.D m hT).J).comp mkG) rfl
    refine uniq.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · have e1 : ψ (MvPolynomial.C a) = cO.D.i a := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.C a))) = mkG (ψ (MvPolynomial.C a))
        rw [e1, hHi, σ.comm]
        rfl
      · have e1 : ψ (MvPolynomial.X i) = cO.t i := by simp [ψ]
        change σ.φ (H (ψ (MvPolynomial.X i))) = mkG (ψ (MvPolynomial.X i))
        rw [e1, hHt, hσ]
        rfl
    · refine RingHom.ext fun x => ?_
      obtain ⟨f, rfl⟩ := E.surjective x
      have a1 := ev_G h cO.D m hT cO.inV hV f
      have a2 := ev_hom σ cL.inV hV f
      rw [hevE] at a1
      rw [← hHe] at a2
      exact a2.symm.trans a1
  have hs' : ∀ x, σ.φ (H x) = mkG x := fun x => RingHom.congr_fun hs x
  let ρ : cL.D.B →+* cL.D.B := Hb.comp σ.φ
  have hρH : ∀ x, ρ (H x) = H x := fun x => by
    change Hb (σ.φ (H x)) = H x
    rw [hs']
    exact hHb x
  have hρi : ∀ r, ρ (cL.D.i r) = cL.D.i r := fun r => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← hHi, hρH]
  have hρt : ∀ i, ρ (cL.t i) = cL.t i := fun i => by
    rw [← hHt, hρH]
  have hle : cL.D.J ≤ cL.D.J.comap ρ := by
    intro x hx
    have : cL.D.J ≤ cL.D.J.comap ρ := by
      conv_lhs => rw [cL.J_eq]
      refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap, hρi, cL.J_eq]
      exact Ideal.mem_map_of_mem _ hr
    exact this hx
  have hθ : Ideal.quotientMap cL.D.J ρ hle = RingHom.id _ := by
    refine quot_eq_id cL c.affine _ (fun r => ?_) (fun f => ?_)
    · rw [Ideal.quotientMap_mk, hρi]
    · rw [← hHe, Ideal.quotientMap_mk, hρH]
  have hid : ρ = RingHom.id _ := by
    refine (GlobalTheory.CompanionTheory.ChartMaps.exists_unique_lift cL cL.D (RingHom.id _) (fun _ => rfl) cL.t (fun _ => rfl)).unique
      ⟨hρi, hρt, RingHom.ext fun x => ?_⟩ ⟨fun _ => rfl, fun _ => rfl, rfl⟩
    have := RingHom.congr_fun hθ (Ideal.Quotient.mk _ x)
    rw [Ideal.quotientMap_mk] at this
    exact this
  refine Function.bijective_iff_has_inverse.2 ⟨Hb, fun x => RingHom.congr_fun hid x, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) cO.D m from y)
  change σ.φ (Hb (Ideal.Quotient.mk _ x)) = _
  rw [hHb, hs']
  rfl

end GlobalTheory.CompanionTheory.DisoHm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmooth
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem contDiffOn_of_right_family : ∀ (n : ℕ) (V P : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (o : P → Mat n → V) (d : (Bool × Fin n × Fin n) → P → P), (∀ v, ∀ z ∈ GLs n, DifferentiableAt ℝ (o v) z) → (∀ v p, ∀ z ∈ GLs n, Rd (bs p) (o v) z = o (d p v) z) → ∀ v, ContDiffOn ℝ ∞ (o v) (GLs n) := by
  intro n V P _ _ o d hdiff hR v
  obtain ⟨A, hA, hfr⟩ := _root_.GlobalTheory.CompanionTheory.PresSobA.Frame.frame n
  let e := Fintype.equivFin (Bool × Fin n × Fin n)
  refine GlobalTheory.CompanionTheory.SmoothVectors.contDiffOn_of_fderiv_family isOpen_GLs o Set.univ
    (fun i => A (e.symm i)) (fun i => hA _) ?_ v (Set.mem_univ v)
  intro u _
  refine ⟨fun i => d (e.symm i) u, fun i => Set.mem_univ _, fun z hz => ?_⟩
  have hD := hfr V (fderiv ℝ (o u) z) z hz
  have hsum : (∑ i, (A (e.symm i) z).smulRight (o (d (e.symm i) u) z))
      = ∑ p, (A p z).smulRight (o (d p u) z) :=
    e.symm.sum_comp (fun p => (A p z).smulRight (o (d p u) z))
  have hval : ∀ p, fderiv ℝ (o u) z (z * bs p) = o (d p u) z := fun p => hR u p z hz
  have h2 : fderiv ℝ (o u) z = ∑ p, (A p z).smulRight (o (d p u) z) :=
    hD.trans (Finset.sum_congr rfl fun p _ => congrArg (fun y : V => (A p z).smulRight y) (hval p))
  exact (hdiff u z hz).hasFDerivAt.congr_fderiv (h2.trans hsum.symm)

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformKernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace TowerAx

theorem exists_X_pow_smul_of {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ}
    {ρ : Fin g → R} {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)]
    [∀ e t S, Module R (T e t S)] {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
    {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S} {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}
    (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)
    (H : TowerAx ρ res p mm) (S : Finset ι) (j : ι) (k : ℕ) :
    ∀ (e : ℕ) (t : ℤ) (a : Ks p e t S), ∃ (t' : ℤ) (b : Ks p e t' S),
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • (H.ops hc S).of e t a =
        (H.ops hc S).of e t' b ∧
      (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1) S) t (a : T (e + 1) t S) =
        GrSum.of (hc (e + 1) S) t' (b : T (e + 1) t' S) := by
  induction k with
  | zero => exact fun e t a => ⟨t, a, by simp, by simp⟩
  | succ k ih =>
    intro e t a
    obtain ⟨t', b, h1, h2⟩ := ih e t a
    refine ⟨t' + 1, H.xK j e t' S b, ?_, ?_⟩
    · rw [pow_succ', mul_smul, h1]
      exact BiOps.X_smul_of (H.ops hc S) j e t' b
    · rw [pow_succ', mul_smul, h2]
      exact GrSum.X_smul_of (hc (e + 1) S) j t' _

end TowerAx

theorem exists_X_pow_smul_eq_zero_of_resTot_eq_zero : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → ∀ (S : Finset ι) (j : ι) (a : H.Tot hc S), S.Nonempty → H.resTot hc S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • a = 0 := by
  intro ι _ R _ g ρ T _ _ res p mm hc H hyp S j a hS hres
  classical
  obtain ⟨s, hs⟩ := (H.ops hc S).exists_finset_sum a
  have hq : ∀ q : ℕ × ℤ, ∃ k : ℕ,
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
        (H.ops hc S).of q.1 q.2 ((H.ops hc S).comp q.1 q.2 a) = 0 := by
    intro q
    have h0 : H.resK q.1 q.2 (Finset.subset_insert j S) ((H.ops hc S).comp q.1 q.2 a) = 0 := by
      rw [← TowerAx.comp_resTot, hres, map_zero]
    have h1 : res (q.1 + 1) q.2 S (insert j S) (Finset.subset_insert j S)
        ((H.ops hc S).comp q.1 q.2 a : T (q.1 + 1) q.2 S) = 0 := congrArg Subtype.val h0
    obtain ⟨k, hk⟩ := hyp (q.1 + 1) S j q.2 _ hS h1
    obtain ⟨t', b, e1, e2⟩ :=
      TowerAx.exists_X_pow_smul_of hc H S j k q.1 q.2 ((H.ops hc S).comp q.1 q.2 a)
    refine ⟨k, ?_⟩
    rw [e2] at hk
    have hb : b = 0 :=
      Subtype.ext (GrSum.of_injective (hc (q.1 + 1) S) t' (by rw [hk]; exact (map_zero _).symm))
    rw [e1, hb, map_zero]
  choose k hk using hq
  refine ⟨∑ q ∈ s, k q, ?_⟩
  rw [hs, Finset.smul_sum]
  refine Finset.sum_eq_zero fun q hqs => ?_
  obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := k)
    (fun _ _ => Nat.zero_le _) hqs)
  rw [hc', pow_add, mul_smul, hk, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL

theorem exists_compact_open_subgroup_subset (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
        (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, hJo, hJU, hJK, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, hJo, (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hJo) hJK, hJU⟩

end GlobalTheory.CompanionTheory.SmGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBoundStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_zeta_special_value_denominator_bound : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctionalStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_linear_functional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ w : ℂ, w ≠ 0 → ‖w‖ * (q : ℝ) ^ 2 < 1 →
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | exact GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | (intros; apply GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral <;> assumption)
end

