module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.GermHodgeLatticeExists

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev sqU : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G ⊗ t.G :=
  lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))

theorem sqPt_left_fst (a : t.G ⊗ t.G ⟶ t.G) :
    (sqPt t x a).left ≫ pullback.fst t.G.hom x = sqMap t x ≫ a.left :=
  pullback.lift_fst _ _ _

theorem fib_ext {T : Over (Sp k)} {a b : T ⟶ GF t x}
    (h : a.left ≫ pullback.fst t.G.hom x = b.left ≫ pullback.fst t.G.hom x) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a).trans (Over.w b).symm

theorem sqPt_psum {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (I : Finset (Fin n)) :
    sqPt t x (psum t.G xs I) = psum (GF t x) (fun i => sqPt t x (xs i)) I := by
  apply fib_ext
  rw [sqPt_left_fst]
  refine Eq.symm (psum_push (isGrpPullback_pullback t.G x) _ xs (sqU t x) (fun i => ?_) I)
  apply Over.OverMorphism.ext
  exact sqPt_left_fst t x (xs i)

theorem sqPt_fst : sqPt t x (fst t.G t.G) = fst (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ fst t.G t.G).left = _
  rw [lift_fst]
  rfl

theorem sqPt_snd : sqPt t x (snd t.G t.G) = snd (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ snd t.G t.G).left = _
  rw [lift_snd]
  rfl

theorem sqPt_comp (b : t.G ⊗ t.G ⟶ t.G) (c : t.G ⟶ t.G) :
    sqPt t x (b ≫ c) = sqPt t x b ≫ (Over.pullback x).map c := by
  apply fib_ext
  rw [sqPt_left_fst, Over.comp_left, Over.comp_left, Category.assoc]
  have A : ((Over.pullback x).map c).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  rw [A, ← Category.assoc (Over.Hom.left (sqPt t x b)), sqPt_left_fst]
  simp only [Category.assoc]

theorem psum_comp_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] {T : Over S} {n : ℕ} (ys : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    psum A ys I ≫ q = psum B (fun i => ys i ≫ q) I :=
  psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) ys I

theorem comp_psum {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {T T' : Over S} (U : T' ⟶ T) {n : ℕ} (ys : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    U ≫ psum B ys I = psum B (fun i => U ≫ ys i) I :=
  psum_hom (preHom U) ys I

section Quot

variable {t x} (Q : AbQuot t x)

abbrev qL : GF t x ⊗ GF t x ⟶ Q.tB.G ⊗ Q.tB.G :=
  lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)

theorem sqPt_psum_q {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (ys : Fin n → (Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G))
    (h : ∀ i, sqPt t x (xs i) ≫ Q.q = qL Q ≫ ys i) (I : Finset (Fin n)) :
    (sqPt t x (psum t.G xs I)).left ≫ Q.q.left = qq Q ≫ (psum Q.tB.G ys I).left := by
  haveI := Q.q_hom
  have e : sqPt t x (psum t.G xs I) ≫ Q.q = qL Q ≫ psum Q.tB.G ys I := by
    rw [sqPt_psum, psum_comp_hom, comp_psum]
    exact congrArg (fun z => psum Q.tB.G z I) (funext h)
  exact congrArg (fun z => z.left) e

theorem sqPt_fst_q : sqPt t x (fst t.G t.G) ≫ Q.q = qL Q ≫ fst Q.tB.G Q.tB.G := by
  rw [sqPt_fst, lift_fst]

theorem sqPt_snd_q : sqPt t x (snd t.G t.G) ≫ Q.q = qL Q ≫ snd Q.tB.G Q.tB.G := by
  rw [sqPt_snd, lift_snd]

theorem sqPt_act_q {b : t.G ⊗ t.G ⟶ t.G} {b' : Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G}
    (h : sqPt t x b ≫ Q.q = qL Q ≫ b') (a : 𝓞 E) :
    sqPt t x (b ≫ t.act.act a) ≫ Q.q = qL Q ≫ b' ≫ Q.tB.act.act a := by
  rw [sqPt_comp, Category.assoc, Q.act_q, ← Category.assoc, h, Category.assoc]

end Quot

theorem adF_fst (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ pullback.fst t.G.hom x = sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i := by
  rcases i with I | I
  · exact sqPt_left_fst t x _
  · exact sqPt_left_fst t x _

theorem adF_q {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ Q.q.left = qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)])
      (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i := by
  rcases i with I | I
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_fst_q Q
    · exact sqPt_act_q Q (sqPt_snd_q Q) _
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_act_q Q (sqPt_fst_q Q) _
    · exact sqPt_snd_q Q

theorem adjunction_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d d' g gB w hw a wL wB hL hB
  exact _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.exists_ratio_iso t.G.left Q.tB.G.left (GF t x).left t.PP.L Q.tB.PP.L (pullback.fst t.G.hom x) Q.q.left
    t.PP.isLB Q.tB.PP.isLB w hw _ _ (adF t x a) _ _ _ _ _ (adF_fst t x a) (adF_q Q a)
    (LB.isGen_pullGen _ _ _ _ hL _) (LB.isGen_pullGen _ _ _ _ hB _)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestriction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Ring

variable (B : Type) [CommRing B] (p : ℕ)

theorem X_pow_dvd_of_mem {P : MvPolynomial Unit B} (hP : P ∈ orig B Unit ^ (p + 1)) :
    (Polynomial.X : Polynomial B) ^ (p + 1) ∣ MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P := by
  have h₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P ∈
      Ideal.map ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
        MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (orig B Unit ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h₁
  have h₂ : Ideal.span (Set.range fun i : Unit => ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
      MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (MvPolynomial.X i)) =
      Ideal.span {(Polynomial.X : Polynomial B)} := by
    congr 1
    ext a
    simp
  rw [h₂, Ideal.span_singleton_pow] at h₁
  exact Ideal.mem_span_singleton.1 h₁

variable {B p}

theorem top_coeff_eq (hp : 1 ≤ p) (b : Fin (p + 1) → B) (v : B)
    (h : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v) : b (Fin.last p) = v := by
  set P : MvPolynomial Unit B := ∑ i : Fin (p + 1), MvPolynomial.C (b i) * MvPolynomial.X () ^ (i : ℕ) -
    (1 + MvPolynomial.X () ^ p * MvPolynomial.C v) with hPdef
  have hP : P ∈ orig B Unit ^ (p + 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, hPdef, map_sub, map_add (f := _), map_sum, map_one, map_mul, map_pow, sub_eq_zero]
    simp only [map_mul, map_pow]
    exact h
  have hd := X_pow_dvd_of_mem B p hP
  have hc := Polynomial.X_pow_dvd_iff.1 hd p (Nat.lt_succ_self p)
  have hp0 : p ≠ 0 := by omega
  have e₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P =
      ∑ i : Fin (p + 1), Polynomial.C (b i) * Polynomial.X ^ (i : ℕ) -
        (1 + Polynomial.C v * Polynomial.X ^ p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hPdef, map_sub, map_add (f := _), map_sum, map_mul, map_pow, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    ring
  have e₂ : ∑ i : Fin (p + 1), (if p = (i : ℕ) then b i else 0) = b (Fin.last p) := by
    rw [Finset.sum_eq_single (Fin.last p)]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro h'
      exact hi (Fin.ext (by simpa using h'.symm))
    · simp
  rw [e₁] at hc
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one, if_neg hp0, e₂, if_true, zero_add] at hc
  exact sub_eq_zero.1 hc

end Ring

theorem appLE_top_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (W : Y.Opens) (h₁ : ⊤ ≤ f ⁻¹ᵁ W)
    (h₂ : ⊤ ≤ g ⁻¹ᵁ W) : f.appLE W ⊤ h₁ = g.appLE W ⊤ h₂ := by
  subst e
  rfl

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appTop = f.appLE ⊤ ⊤ h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Test

variable {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0)
variable {B : Type} [CommRing B] [Algebra k B]

theorem rQ_appLE_prZ (p : ℕ) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W)
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W)) (a : Γ(pullback G.hom x, W)) :
    ((rQ G x p z).appLE _ ⊤ hr).hom (((prZ G x p).app W).hom a) =
      ((spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop).hom
        (((xkZ G x z).appLE W ⊤ hW).hom a) := by
  have h₁ : (prZ G x p).app W ≫ (rQ G x p z).appLE _ ⊤ hr = (rQ G x p z ≫ prZ G x p).appLE W ⊤ hr := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have h₂ : (xkZ G x z).appLE W ⊤ hW ≫
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop =
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p) ≫ xkZ G x z).appLE W ⊤ (by
        rw [Scheme.Hom.comp_preimage]
        exact fun y _ => hW (show _ from trivial)) := by
    rw [← Scheme.Hom.appLE_comp_appLE _ _ W ⊤ ⊤ hW (by simp), appTop_eq_appLE _ (by simp)]
  have h₃ := h₁.trans ((appLE_top_congr (rQ_prZ G x p z) W _ _).trans h₂.symm)
  exact congrArg (fun q => q.hom a) h₃

theorem rQ_appLE_dltOn (p : ℕ) (z : overAt x B ⟶ G) (V : (Ym G x p).Opens) (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ V) :
    ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = toΓ _ (dQ B p) := by
  have h₁ : (Ym G x p).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (rQ G x p z).appLE V ⊤ hr =
      (rQ G x p z).appTop := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h₂ : ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = ((rQ G x p z).appTop).hom (dlt G x p) :=
    congrArg (fun q => q.hom (dlt G x p)) h₁
  have h₃ := congrArg (fun q => (q.appTop).hom (toΓ (Jet k Unit p) (Ideal.Quotient.mk _ (MvPolynomial.X ()))))
    (rQ_fst G x p z)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h₃
  rw [h₂, dlt, h₃, spMap_toΓ]
  congr 1
  exact MvPolynomial.aeval_X (R := k) (fun _ : Unit => dQ B p) ()

theorem coef_at_test (p : ℕ) (hp : 1 ≤ p) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens)
    (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B)
    (hf : f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ))
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W))
    (hv : ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v)) :
    ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  have hs : ∀ i, ∃ b : B, toΓ B b = ((xkZ G x z).appLE W ⊤ hW).hom (c i) := fun i =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2 _
  choose b hb using hs
  have key : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v := by
    apply toΓ_inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, hf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, rQ_appLE_prZ G x p z W hW hr, rQ_appLE_dltOn, ← hb, spMap_toΓ]
    rfl
  rw [← hb, top_coeff_eq hp b v key]

end Test

theorem coef_pull : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  intro X0 G _ k _ x p hp B _ _ z W hW c f v hf hr hv
  exact coef_at_test G x p hp z W hW c f v hf hr hv

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeLatticeGermSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_gives_hodgeLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ _hcg hact hfree
  classical
  have hρeq : ∀ (a : 𝓞 E) (v : Fin d → Ω),
      (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec v = ρ a v := fun a v =>
    M.inj ((S.act₀ a v).trans (hact a v).symm)
  obtain ⟨⟨ρ0, hρ0⟩, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint Ω d (𝓞 E) S.g₀.B
  let dd : ((Fin d → Ω) × (Fin d → Ω)) ≃ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
    PositivityTheory.Xgn.GermHodgeLattice.dd Ω d
  have hdd : ∀ y, dd y = (y.1, dotProductBilin Ω Ω y.2) := fun y =>
    PositivityTheory.Xgn.GermHodgeLattice.dd_apply y
  have hsymm : ∀ y, ((dd.symm y).1, dotProductBilin Ω Ω (dd.symm y).2) = y := fun y => by
    rw [← hdd]; exact dd.apply_symm_apply y
  have hr1 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).1 = (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  have hr2 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).2 =
        (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B (star a)).transpose.mulVec z.2 -
          (GlobalTheory.CompanionTheory.Ar.Conj.bil (S.g₀.B.ad a) 1 1).transpose.mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  let ρH : 𝓞 E →+* Module.End Ω ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) :=
    { toFun := fun a => dd.toLinearMap ∘ₗ ρ0 a ∘ₗ dd.symm.toLinearMap
      map_one' := LinearMap.ext fun y => by simp
      map_mul' := fun a b => LinearMap.ext fun y => by simp [Module.End.mul_apply]
      map_zero' := LinearMap.ext fun y => by simp
      map_add' := fun a b => LinearMap.ext fun y => by simp }
  have hρH : ∀ a y, ρH a y = dd (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a (dd.symm y)) := by
    intro a y; show dd (ρ0 a (dd.symm y)) = _; rw [hρ0]
  let HL : GlobalTheory.CompanionTheory.Ar.Lat ξ ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) := fun p =>
    Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ p))
      (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)))
  have hmem : ∀ p y, dd y ∈ HL p ↔
      y ∈ GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) := by
    intro p y
    constructor
    · intro h
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp h
      have : z = y := dd.injective hzy
      exact this ▸ hz
    · intro h
      exact Submodule.mem_map.mpr ⟨y, h, rfl⟩
  have hiso := fun p => _root_.GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing Ω d (𝓞 E) S.g₀.B (S.BK p) (S.φ p) (S.ψ p) (S.lam p) (S.iso p)
  have h_fst : ∀ (a : 𝓞 E) (y : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)),
      ((ρH a) y).1 = (ρ a) y.1 := by
    intro a y
    rw [hρH, hdd]
    dsimp only
    rw [hr1, ← hρeq]
    congr 1
  have h_inr : ∀ (a : 𝓞 E) (f : Module.Dual Ω (Fin d → Ω)),
      (ρH a) (0, f) = (0, f ∘ₗ ρ (H.bar a)) := by
    intro a f
    rw [hρH, hdd]
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz ⊢
    obtain ⟨hz1, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [hr1, hz1, Matrix.mulVec_zero]
    · dsimp only
      rw [hr2, hz1, Matrix.mulVec_zero, sub_zero]
      refine LinearMap.ext fun u => ?_
      simp only [dotProductBilin_apply_apply, LinearMap.comp_apply, ← hρeq,
        Matrix.mulVec_transpose, hstar]
      exact (Matrix.dotProduct_mulVec _ _ _).symm
  have h_map : GlobalTheory.CompanionTheory.Ar.Lat.map HL
      (LinearMap.fst Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat := by
    funext p
    ext e
    rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p,
      ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (S.φ p) (S.ψ p)
        (S.lam p) e]
    show e ∈ Submodule.map _ (HL p) ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨z, hz, by simp [hdd]⟩
    · rintro ⟨z, hz, rfl⟩
      exact Submodule.mem_map.mpr ⟨dd z, (hmem p z).mpr hz, by simp [hdd]⟩
  have h_comap : GlobalTheory.CompanionTheory.Ar.Lat.comap HL
      (LinearMap.inr Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat.dual := by
    funext p
    ext f
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz
    obtain ⟨-, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) ∈ HL p ↔
      ∀ e ∈ M.lat p, dotProductBilin Ω Ω z.2 e ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ p
    rw [show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) = dd (0, z.2) from (hdd (0, z.2)).symm,
      hmem, PositivityTheory.Xgn.GermHodgeLattice.inr_stdLat _ _ _ _ hl1 hl2,
      PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p]
    simp only [dotProductBilin_apply_apply]
  refine ⟨GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.mk ρH HL h_fst h_inr h_map h_comap ?_ ?_, ?_⟩
  · intro p
    obtain ⟨x₀, hli, hsp⟩ := hfree p
    obtain ⟨hl1, hl2, hbij, -, hint, -⟩ := hiso p
    obtain ⟨s, hs, hst⟩ :=
      PositivityTheory.Xgn.GermHodgeLattice.exists_finite (GlobalTheory.CompanionTheory.Ar.genMap ξ p) _ hsp
    obtain ⟨U, hpU, hU⟩ := PositivityTheory.Xgn.GermHodgeLattice.exists_open p s hs
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    have hspanT := PositivityTheory.Xgn.GermHodgeLattice.span_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) hbij.2
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (fun r' _ => (GlobalTheory.CompanionTheory.Ar.genMap ξ p).mem_range_self r')
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)), Submodule.span_span_of_tower] at hspanT
    have hcard := PositivityTheory.Xgn.GermHodgeLattice.card_eq _ hli hsp
    have hfin : Module.finrank Ω ((Fin d → Ω) × (Fin d → Ω)) = d + d := by simp
    have hG_li := linearIndependent_of_top_le_span_of_card_eq_finrank hspanT.ge
      (hcard.trans hfin.symm)
    have hF_li := hG_li.map' dd.toLinearMap dd.ker
    have hF_span := congrArg (Submodule.map dd.toLinearMap) hspanT
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at hF_span
    simp only [Function.comp_def, LinearEquiv.coe_coe] at hF_span hF_li
    have hfam : ∀ (b : 𝓞 E) (j : Fin r),
        ρH b (dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ j)))) =
        dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p)
            (GlobalTheory.CompanionTheory.Ar.Conj.rhoH (S.g p).B b (x₀ j)))) := by
      intro b j
      rw [hρH, LinearEquiv.symm_apply_apply]
      exact congrArg dd ((LinearMap.congr_fun (hint b) _).trans
        (congrArg (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))
          (PositivityTheory.Xgn.GermHodgeLattice.rhoH_mp _ (S.mapK p) b (x₀ j))))
    refine ⟨U ⊓ U', ⟨hpU, hpU'⟩, fun i => dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
      (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ i))), fun q hq => ?_⟩
    have hHL : HL q = Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ q))
        (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q)
          (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))) := by
      show Submodule.map _ _ = _
      rw [hU' q hq.2]
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (hU q hq.1), Submodule.map_span, ← Set.range_comp] at hHL
    simp only [Function.comp_def, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hHL
    unfold GlobalTheory.CompanionTheory.Ar.HT.IsFreeOn
    simp only [hfam]
    refine ⟨hF_li, ?_, hHL⟩
    rw [hHL, Submodule.span_span_of_tower]
    exact hF_span
  · intro p _
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hfr : Module.finrank Ω (Fin d → Ω) = d := Module.finrank_fin_fun Ω
    have hinjP : Function.Injective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro u v huv
      have h := congrArg (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1)) huv
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl2] using h
    have hsurjP : Function.Surjective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro v
      refine ⟨(GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1).mulVec v, ?_⟩
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl1]
    have hcg : (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) =
        (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) ∘ (Pi.basisFun Ω (Fin d)) := by
      funext l; simp [Matrix.toLin'_apply]
    have hc_li : LinearIndependent Ω
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) := by
      rw [hcg]
      exact (Pi.basisFun Ω (Fin d)).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinjP)
    have hc_span : Submodule.span Ω (Set.range
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1))) = ⊤ := by
      rw [hcg, Set.range_comp, ← Submodule.map_span, (Pi.basisFun Ω (Fin d)).span_eq,
        Submodule.map_top, LinearMap.range_eq_top.mpr hsurjP]
    refine ⟨U', hpU',
      (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) ∘ (finCongr hfr),
      ?_, ?_⟩
    · rw [(finCongr hfr).surjective.range_comp]; exact hc_span
    · intro q _ hq
      unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt
      refine ⟨hc_li.comp _ (finCongr hfr).injective, ?_⟩
      rw [(finCongr hfr).surjective.range_comp]
      ext e
      rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S q,
        ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (S.φ q) (S.ψ q)
          (S.lam q) e,
        ← hU' q hq, PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat]
  · unfold GlobalTheory.CompanionTheory.Ar.Flat.GermSys.Gives
    refine ⟨fun a y => ?_, fun p y => ?_⟩
    · show ρH a (y.1, dotProductBilin Ω Ω y.2) = _
      rw [show (y.1, dotProductBilin Ω Ω y.2) = dd y from (hdd y).symm, hρH,
        LinearEquiv.symm_apply_apply, hdd]
    · show (y.1, dotProductBilin Ω Ω y.2) ∈ HL p ↔ _
      rw [← hdd]
      exact hmem p y

end GlobalTheory.CompanionTheory.Ar.Flat
end

