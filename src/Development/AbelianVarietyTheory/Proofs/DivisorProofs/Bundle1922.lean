module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallSpan

variable {D : D7} {m n : ℕ}


open GlobalTheory.ExportSeries.Onto in
theorem exists_harm (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (F : VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n) := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle (Submodule.mem_map_of_mem F.2)


open GlobalTheory.ExportSeries.HarmLattice in
theorem harmLat_le_span {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O O' : Subring ℂ) (hO' : ∀ a : 𝓞 K, σ a ∈ O') (w : Weight D n) (B : GLR D n)
    (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hM : Submodule.IsFullLattice D.host.E M) {P : PolF D m n} (hP : P ∈ harmLat σ (fun τ => f.comp (emb τ)) O' m w B M) :
    P ∈ Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n)) := by
  set N := Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n))
  have hN : N ≤ (harm m w B).restrictScalars O' := Submodule.span_le.2 fun Q hQ => hQ.1
  have hle : coefLatFn σ (fun τ => f.comp (emb τ)) O' w.lam M ≤ N.map ((harmFn m w B).restrictScalars O') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' := GlobalTheory.NabBC.nabBaseChange _ _ _ _ n f emb w.lam M hM hF
    rw [coefFn_eq, SetLike.mem_coe]
    clear hF
    induction hF' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, e⟩ := hy
      obtain ⟨Q, hQ, eQ⟩ := exists_harm w B hw hm (GlobalTheory.CoefModel.mapVV (σ.comp f) w.lam x)
      have e1 : harmFn m w B Q = coefFn (σ.comp f) w.lam (x : Pol K₀ D.what₂.Tau n) := eQ.trans (coefFn_eq _ _ x).symm
      refine ⟨Q, Submodule.subset_span ⟨hQ, ?_⟩, ?_⟩
      · exact Submodule.subset_span ⟨x, hx, e1⟩
      · refine eQ.trans (congrArg (cf w.lam) (Subtype.ext ?_))
        change MvPolynomial.map (σ.comp f) x.1 = MvPolynomial.map σ y.1
        rw [e, MvPolynomial.map_map]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hO' a⟩ : O') h1
  obtain ⟨Q, hQ, e⟩ := hle hP.2
  have h0 : P - Q = 0 := GlobalTheory.ExportSeries.HarmInj.harm_inj D m n w B hw hm _ (sub_mem hP.1 (hN hQ)) (by
    rw [map_sub, sub_eq_zero]
    exact e.symm)
  rw [sub_eq_zero.1 h0]
  exact hQ

theorem isLattice_latAt {S T : HSp D} {B : Base S T} (hF : B.F.Good) (h : Bridge.Gf S) :
    Submodule.IsFullLattice D.host.E (B.latAt h) :=
  by
  classical
  have hspan : Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E)) = ⊤ := by
    let W := Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E))
    change W = ⊤
    by_contra hW
    let g : (Fin S.rank → D.host.E) →ₗ[D.host.E] Module.Dual D.host.E W :=
      { toFun := fun x => { toFun := fun y => ∑ i, ∑ j, x i * S.gram i j * y.1 j
                            map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
                            map_smul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
        map_add' := by intros; ext y; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := by intros; ext y; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (Fin S.rank → D.host.E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let v : Fin S.rank → D.host.E := fun i => star (x i)
    have hv0 : v ≠ 0 := by
      intro hv
      apply hx0
      funext i
      have hi := congrFun hv i
      simpa [v] using congrArg star hi
    have hline (r : D.host.E) : r • v ∈ B.F.ΛS := by
      apply (hF.sdS.2 _).2
      intro y hy
      have hz : (∑ i, ∑ j, x i * S.gram i j * y j) = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      have hzy : (∑ i, ∑ j, star (y i) * S.gram i j * v j) = 0 := by
        have hg (i j : Fin S.rank) : star (S.gram i j) = S.gram j i := by
          exact S.herm.eq _ _
        have hs : (starRingEnd D.host.E) (∑ i, ∑ j, x i * S.gram i j * y j) = 0 := by rw [hz, map_zero]
        simp only [map_sum, map_mul] at hs
        change (∑ i, ∑ j, star (x i) * star (S.gram i j) * star (y j)) = 0 at hs
        simp only [hg] at hs
        rw [Finset.sum_comm] at hs
        simpa [mul_comm, mul_left_comm, mul_assoc] using hs
      refine ⟨0, ?_⟩
      simp only [map_zero, Pi.smul_apply, smul_eq_mul]
      calc
        0 = r * (∑ i, ∑ j, star (y i) * S.gram i j * v j) := by rw [hzy, mul_zero]
        _ = ∑ i, ∑ j, star (y i) * S.gram i j * (r * v j) := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hn
      apply hv0
      funext i
      simpa using not_exists.mp hn i
    let coord := (LinearMap.proj i : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E).restrictScalars (𝓞 D.host.E)
    have htop : B.F.ΛS.map coord = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
    have : Module.Finite (𝓞 D.host.E) D.host.E := Module.finite_def.mpr (htop ▸ hF.sdS.1.fg.map coord)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  exact Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hspan _

end GlobalTheory.SmallSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbedding
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif

namespace GlobalTheory.ConjTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {s s₁ : Sp ℂ ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s₁}

theorem cjPt_act (m : ObjMap o₁ o cj) (x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G) (a : 𝓞 E) :
    cjPt m.cart (x ≫ o.t.act.act a) = cjPt m.cart x ≫ o₁.t.act.act a := by
  refine pt_ext m.cart ((cjPt_comp _ _).trans ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc (cjPt m.cart x).left, cjPt_comp]
  exact (Category.assoc _ _ _).symm

theorem cjPt_eta (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.eta a) = o₁.eta a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.eta a).symm)

theorem cjPt_etaA (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.etaA a) = o₁.etaA a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.etaA a).symm)

theorem exists_unif (m : ObjMap o₁ o cj) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hA : u.IsAH Hm κ) :
    ∃ (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (κ₁ : u₁.Λ → ℂ), u₁.IsAH (Hm.map star) κ₁ ∧
      (∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) ∧ ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)) := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw', -⟩ := exists_inv w hw
  have hP := pull_isLB o.t.PP.isLB m.cm.F
  exact ⟨carry (conjPull m.cart u) hP o₁.t.PP.isLB hw', _,
    carry_isAH hP o₁.t.PP.isLB hw' (conjPull_isAH m.cart u hA), fun _ => Iff.rfl, fun _ => rfl⟩

theorem herm_map_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (herm (Hm.map star) z w).im = -(herm Hm (star z) (star w)).im := by
  rw [herm, herm, ← star_form]
  rfl

def conjEquiv (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := (starL' ℝ (A := Fin g → ℂ)).toLinearEquiv

theorem conjEquiv_apply {g : ℕ} (z : Fin g → ℂ) : conjEquiv g z = star z := rfl

theorem isTransport_conj {s' s₁' : Sp ℂ ⟶ Sp B} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) φ) :
    IsTransport o o' u u' Hm Hm' ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, ← hΛ', h1, hΛ, star_star]
  · refine cjPt_injective m'.cart ?_
    rw [e, e, cjPt_act, ← hx', ← hx']
    refine h2 a _ _ ?_
    rw [hx, hx, star_star, star_star, hw, cjPt_act]
  · have := h3 (star z) (star w)
    rw [herm_map_star, herm_map_star, star_star, star_star] at this
    rw [e, e]
    exact neg_injective this
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_eta]
    refine h4 a _ ?_
    rw [hx, star_star, hz, cjPt_eta]
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_etaA]
    refine h5 a _ ?_
    rw [hx, star_star, hz, cjPt_etaA]

theorem exists_conj_obj (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s),
      Nonempty (ObjMap o₁ o cj) ∧ Nonempty (ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)) := by
  obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _
    ((cj ≫ y) ≫ toX Xo c ≫ Xo.s) cj rfl rfl
    (by rw [DetExtendZero.spMap_id, Category.comp_id, Category.assoc]) o
  obtain ⟨k, -⟩ := ObjComp.objMap_comp n m
  exact ⟨o₁, ⟨m⟩, by rw [Category.assoc cj y (toX Xo c)]; exact ⟨k⟩⟩

end GlobalTheory.ConjTransport

namespace GlobalTheory

open ConjTransport

theorem hasTransport_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ)
    (h : HasTransport Xo c U ((starRingEnd ℂ).comp e)) : HasTransport Xo c U e := by
  rintro y y' hy hy' hU hU' o o' ⟨n⟩ ⟨n'⟩ g g' u u' Hm Hm' κ κ' hA hA'
  obtain ⟨o₁, ⟨m⟩, k⟩ := exists_conj_obj Xo c y o n
  obtain ⟨o₁', ⟨m'⟩, k'⟩ := exists_conj_obj Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  have a : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e →
      (cj ≫ y) ≫ toF Xo c = spMap ((starRingEnd ℂ).comp e) := fun y hy => by
    rw [Category.assoc, hy, DetExtendZero.spMap_comp]
  have r : ∀ y : Sp ℂ ⟶ Xo.XF c, Set.range y ⊆ U → Set.range (cj ≫ y) ⊆ U := by
    rintro y hy _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hy ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := h (cj ≫ y) (cj ≫ y') (a y hy) (a y' hy') (r y hU) (r y' hU') o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁'
    hA₁ hA₁'
  exact ⟨_, isTransport_conj m m' hΛ hx hΛ' hx' hφ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerateStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₁ → (h.geo f₁ f₂ th k).Birational := by
  first | exact @GlobalTheory.HSApp.birational_of_ratGen | exact GlobalTheory.HSApp.birational_of_ratGen | (intros; apply GlobalTheory.HSApp.birational_of_ratGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFunctionValuesClassicalUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.MBLow.Cl.HolB

variable {X Y : Scheme.{0}}

theorem valF_comp_app (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valF x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valF (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dite_eq_left h', dite_eq_left h]
    simp only [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [valF, valF, dite_eq_right h', dite_eq_right h]

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := rfl

def psiB (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left)
    (hw : φ ≫ D.P.A.hom = x.P.A.hom ≫ spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) :
    x.P.A.left ⟶ (DegPre.BF D ℂ).left :=
  (lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
    (Over.homMk φ (by
      rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
      Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A)).left

theorem hol_ptB : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  intro R _ _ _ D N ν g d x u φ hφ hE U f
  have hw := hφ.1.w
  have key : ∀ z, ptB ν d z = (u.ex z).left ≫ psiB R D x φ hw := by
    intro z
    have h0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := Over.w (u.ex z)
    let e : TF (R := R) ℂ ⟶ Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) :=
      Over.homMk (u.ex z).left (by simp only [Over.mk_hom]; rw [← Category.assoc, h0]; exact Category.id_comp _)
    have he : e ≫ lift (Over.homMk x.P.A.hom rfl : Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ TF (R := R) ℂ)
        (Over.homMk φ (by
          rw [hw]; simp only [Over.mk_hom, TF, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) :
          Over.mk (x.P.A.hom ≫ (TF (R := R) ℂ).hom) ⟶ D.P.A) = lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex z)) := by
      rw [comp_lift]
      congr 1
      · ext; simp [e, h0]
      · ext; simp [e, hE z]
    rw [ptB, ← he]
    rfl
  have hs : {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (psiB R D x φ hw ⁻¹ᵁ U)} := by
    ext z
    simp only [Set.mem_setOf_eq, key z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := u.hol (psiB R D x φ hw ⁻¹ᵁ U) ((psiB R D x φ hw).app U |>.hom f)
  rw [hs]
  refine ⟨ho, hd.congr fun z _ => ?_⟩
  rw [← valF_eq_valAt', valF_comp_app, key z]

end GlobalTheory.MBLow.Cl.HolB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProduct
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory
theorem howeAlg_fock_tensor : ∀ (T : Type) [Fintype T] [DecidableEq T] (P Q R S : T → ℕ) (x : T → ℂ), HoweAlg (fun w => actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (tensAny fun w => coinv (P w) (Q w) (R w) (S w) (x w)) := by
  intro T _ _ P Q R S x
  exact _root_.GlobalTheory.HoweR.howeAlg_tensAny T (fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) _ _ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) (fun w => coinv (P w) (Q w) (R w) (S w) (x w)) (fun w => _root_.GlobalTheory.HoweR.fock_pack (P w) (Q w) (R w) (S w) (x w))
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatInf
open TensorProduct

theorem map_eq_baseChange {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (K : Ideal R) :
    Ideal.map (algebraMap R S) K =
      (K.baseChange S).map ((Algebra.TensorProduct.rid R S S).toLinearEquiv : S ⊗[R] R →ₗ[S] S) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Ideal.map]
  congr 1
  ext y
  simp [Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem map_inf_of_flat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (I J : Ideal R) : Ideal.map f (I ⊓ J) = Ideal.map f I ⊓ Ideal.map f J := by
  letI := f.toAlgebra
  haveI : Module.Flat R S := hf
  have e : f = algebraMap R S := rfl
  rw [e, map_eq_baseChange, map_eq_baseChange, map_eq_baseChange, GlobalTheory.baseChange_inf,
    Submodule.map_inf _ (Algebra.TensorProduct.rid R S S).toLinearEquiv.injective]

end GlobalTheory.FlatInf

namespace GlobalTheory.FlatInf

theorem comap_inf_of_flat : ∀ (W V : Scheme.{0}) (g : V ⟶ W), Flat g →
    ∀ a b : W.IdealSheafData, (a ⊓ b).comap g = a.comap g ⊓ b.comap g := by
  intro W V g hg a b
  haveI := hg
  have hU : ∀ y : V, ∃ U : W.affineOpens, g y ∈ U.1 := fun y => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show g y ∈ ((⊤ : W.Opens) : Set W) from trivial) (⊤ : W.Opens).isOpen
    exact ⟨⟨U, hU⟩, hyU⟩
  choose U hyU using hU
  have hA : ∀ y : V, ∃ A : V.affineOpens, y ∈ A.1 ∧ A.1 ≤ g ⁻¹ᵁ (U y).1 := fun y => by
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAle⟩ := V.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ ((g ⁻¹ᵁ (U y).1 : V.Opens) : Set V) from hyU y) (g ⁻¹ᵁ (U y).1).isOpen
    exact ⟨⟨A, hA⟩, hyA, hAle⟩
  choose A hyA hAU using hA
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply,
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
    exact map_inf_of_flat _ (g.flat_appLE (U y).2 (A y).2 (hAU y)) _ _

end GlobalTheory.FlatInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSectionProjectiveOverField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem secClosed_closedPoint (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X)
    (_hq : IsProjOver q) (hz : z ≫ q = 𝟙 _) :
    IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id q z hz
  have hc : IsClosed (Set.range z.base) := z.isClosedEmbedding.isClosed_range
  convert hc using 1
  ext x
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim y (IsLocalRing.closedPoint K)]

end GlobalTheory
end

