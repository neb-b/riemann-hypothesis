module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7}

variable (T : Top D)

namespace Top

abbrev PtA (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  PtV (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) (T.G.PY j (WeightAlgebra.resCh la)) (T.G.lies j la) la

def th (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) := thGen (T.Q.Xo j) T.Q.c (T.nab j) (wtA w) w.n

def sh (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) :=
  shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (wtA w) w.n (T.dδ j w.n)

end Top

variable {T} (h : LawsP T)

def recPJ (j : ℕ) (hj : InR D j) : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  mkX T.Q.eO T.C h.toLawsCore.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.toLawsCore.Nl h.toLawsCore.hNs
    h.toLawsCore.hNl h.toLawsCore.hle T.Cu T.Xc T.Xc_lat T.FJt h.toLawsCore.sg
    T.G.P j hj (h.toLawsCore.mul j hj) (T.G.dat j) (fun hm => (h.datum_condition j hj.1 hm).1) (fun hm => (h.datum_condition j hj.1 hm).2)
    (T.PtA j) (fun _ y => imgV y) (fun _ y => vAtV y) (fun _ y => isVal_vAt y)
    (fun _ f _ => nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) f) (T.th j) (T.sh j)

def recX : WeightAlgebra.Prov D (recB h.toLawsCore) T.G.P := fun j h1 h2 => recPJ h j ⟨h1, h2⟩

theorem recPJ_vAt_inc (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la)
    (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) :
    (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 := by
  dsimp only [recPJ, mkX, vG, incG]
  refine le_antisymm (iInf_le_of_le (deg w) (le_of_eq ?_)) (le_iInf fun m => ?_)
  · change vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff (deg w)) = _
    first
      | simp [AddMonoidAlgebra.coeff_single]
      | simp [AddMonoidAlgebra.single_apply]
      | simp [Finsupp.single_apply]
      | exact (0 : Nat)
  · change _ ≤ vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff m)
    by_cases hm : deg w = m
    · subst hm
      first
        | simp [AddMonoidAlgebra.coeff_single]
        | simp [AddMonoidAlgebra.single_apply]
        | simp [Finsupp.single_apply]
    · first
        | simp [AddMonoidAlgebra.coeff_single, hm]
        | simp [AddMonoidAlgebra.single_apply, hm]
        | simp [Finsupp.single_apply, hm]
      rw [(isVal_vAt y).zero]
      exact le_top

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Field

variable (c c' : Coeff l) (hle : c.F ≤ c'.F)

abbrev incF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def AlgOver (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (incF c c' hle a) = algebraMap c.F S a

variable {c c'}

theorem embK_incF (τ : E →+* ℂ) (a : 𝓞 E) : incF c c' hle (embK c τ a) = embK c' τ a :=
  Subtype.ext rfl

theorem sOf_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) :
    sOf c' S = sOf c S := by
  unfold sOf
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact h ((IntermediateField.inclusion c.le).toRingHom x)

variable {Xo : Moduli Dw l}

theorem isEigAt_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (τ : E →+* ℂ) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c' τ v ↔ IsEigAt (Xo := Xo) c τ v := by
  have key : ∀ a : 𝓞 E, algebraMap c'.F S (embK c' τ a) = algebraMap c.F S (embK c τ a) := by
    intro a
    rw [← embK_incF hle τ a]
    exact h (embK c τ a)
  unfold IsEigAt
  simp only [key]

def FrPt.res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : FrPt Xo c S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h)
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).1 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).2 he)
  s := y.s
  gen := y.gen

def FrPt.ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : FrPt Xo c' S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).1 he)
  s := y.s
  gen := y.gen

theorem FrPt.res_ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : (y.ext hle h).res hle h = y := rfl

variable {r : ℕ}

def unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  { Comp := (U (σ'.comp (incF c c' hle))).Comp
    fin := (U (σ'.comp (incF c c' hle))).fin
    X := (U (σ'.comp (incF c c' hle))).X
    un := fun k x => FrPt.ext hle (S := CAt σ') (fun _ => rfl) ((U (σ'.comp (incF c c' hle))).un k x) }

def IsBC {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
    evR Xo c' f' y = ∑ i, algebraMap c'.F S (as i) * evR Xo c (fs i) (y.res hle h)

def CuspBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cusp Xo c U a n) ∧ IsBC hle f' as fs

def ActBC {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') :
    Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) →
    IsBC hle f' as fs → IsBC hle (act' g f') as (fun i => act g (fs i))

end Field

section Comparison₂

variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} {r : ℕ}
  {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def OneMapTieC (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (cc : (unfBC hle U σ0').Comp → ℂ)
    (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspBC hle U ∧ ActBC hle act act' ∧
    OneMapRow Xo c' V (unfBC hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph

end Comparison₂

end Gen

section Dict

open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {n r : ℕ}

def MarkBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ}
    {lab : Fin g → D.host.E →+* ℂ} (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (h γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w

def CXiVal {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ∀ t : Tup, IsUnf (U₂ t) ∧ (∀ k, ModelW V hr ((U₂ t).X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif (dδ t).Xo₂ ((σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)).comp
          (IntermediateField.inclusion (dδ t).c₂.le).toRingHom)
        (fun j => relab (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) (e j).1))
      (ik : (U₂ t).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U₂ t).X k).Λ)
      (th : ∀ k, ((U₂ t).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat (U₂ t) V hr (dict₂ t) ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy (U₂ t) V hr (dict₂ t) ι F ik φ h γ →
        rdU (U₂ t) (dδ t).cδ (dict₂ t h).1 (dict₂ t h).2 =
          c0 * ((xi t (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F)

def actLev (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
    levActR (Xo := Xo) (c := c) lev g' y y') g

def ActLev (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g' y y')

end Dict

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ValuedUnif
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain WithZero

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem valued_unif (la : HeightOneSpectrum (𝓞 B.KO)) :
    Valued.v ((unif X la : X.Ol la) : X.Kl la) = exp (-1 : ℤ) := by
  have hu : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.intValuation_exists_uniformizer la
  have hπv : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = exp (-1 : ℤ) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := B.KO) (v := la) π
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ] at h
    exact h
  set o : X.Ol la := algebraMap (𝓞 B.KO) (X.Ol la) π with ho
  have ho0 : o ≠ 0 := by
    intro h0
    have : Valued.v ((o : X.Ol la) : X.Kl la) = 0 := by rw [h0]; simp
    have h2 : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = 0 := this
    rw [hπv] at h2
    exact exp_ne_zero h2
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
  have hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit
  have hv0 : Valued.v ((unif X la : X.Ol la) : X.Kl la) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h0
    exact hu.ne_zero (Subtype.ext h0)
  have e1 : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-1 : ℤ) := hπv
  rw [hk] at e1
  push_cast at e1
  rw [map_mul, map_pow, hu1, one_mul, ← exp_log hv0, ← exp_nsmul, exp_inj] at e1
  have h2 : (k : ℤ) * (-log (Valued.v ((unif X la : X.Ol la) : X.Kl la))) = 1 := by
    rw [nsmul_eq_mul] at e1; linarith
  have hk1 : (k : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
  rw [hk1, one_mul] at h2
  rw [← exp_log hv0]
  congr 1
  linarith

theorem valued_Ol (la : HeightOneSpectrum (𝓞 B.KO)) (o : X.Ol la) (m : ℕ)
    (hm : IsDiscreteValuationRing.addVal (X.Ol la) o = m) : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-(m : ℤ)) := by
  have hu : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have ho0 : o ≠ 0 := by
    rintro rfl; rw [IsDiscreteValuationRing.addVal_zero] at hm; exact ENat.top_ne_natCast m hm
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
  rw [IsDiscreteValuationRing.addVal_def' u hu n, Nat.cast_inj] at hm
  subst hm
  have hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit
  push_cast
  rw [map_mul, map_pow, hu1, one_mul, valued_unif, ← exp_nsmul]
  congr 1
  simp

section Kap

variable {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
  {la : HeightOneSpectrum (𝓞 B.KO)} (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
  (ζ : PtsG G la) [IsDVRAt ζ] (T : CDVR) (ι : Loc ζ →+* T.V) (hι : AddValPres ζ ι)

def kapA : Kp (xplus X E hM) la G.N →+* T.Fr :=
  (phiAt ζ T.Fr ι h hι).comp (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))

theorem kapA_Op (y : Op (xplus X E hM) la G.N) :
    kapA h ζ T ι hι (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _ y) =
      algebraMap T.V T.Fr (ι (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) y)) := by
  show phiAt ζ T.Fr ι h hι (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)
    (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _ y)) = _
  rw [← IsScalarTower.algebraMap_apply (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)]
  have e : algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) y =
      ((algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y :
        ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) : OsK (xplus X E hM) la G.w) := rfl
  rw [e, phiAt_coe]
  show algebraMap T.V T.Fr (ι (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ)
    (algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y))) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem unifO_irr : Irreducible (unifO (xplus X E hM) la G.N) :=
  Op.irreducible_map _ _ _ (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la)))

theorem vV_kapA_Op (y : Op (xplus X E hM) la G.N) (k : ℕ) (hk : IsDiscreteValuationRing.addVal _ y = k) :
    vV T.V (kapA h ζ T ι hι (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _ y)) =
      ((ep (unifO (xplus X E hM) la G.N) ζ * k : ℕ) : ℤ) := by
  have hϖ := unifO_irr (E := E) (hM := hM) (G := G) (la := la)
  have hy : y ≠ 0 := by
    rintro rfl; rw [IsDiscreteValuationRing.addVal_zero] at hk; exact ENat.top_ne_natCast k hk
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, Nat.cast_inj] at hk
  subst hk
  rw [kapA_Op]
  apply vV_alg_of_addVal
  have hep : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (unifO (xplus X E hM) la G.N)) =
      (ep (unifO (xplus X E hM) la G.N) ζ : ℕ∞) := by
    rw [coe_ep ζ h, vL_eq_addVal, ← IsScalarTower.algebraMap_apply]
  have hu0 : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (u : Op (xplus X E hM) la G.N)) = 0 := by
    rw [← IsUnit.unit_spec (u.isUnit.map (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ)))]
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  rw [hι, map_mul, map_pow, AddValuation.map_mul, AddValuation.map_pow, hep, hu0]
  push_cast
  ring

theorem overLa_kapA : OverLa la T.V ((kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp
    (algebraMap B.KO ((xplus X E hM).Kl la)))) (ep (unifO (xplus X E hM) la G.N) ζ) := by
  set io := (kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp
    (algebraMap B.KO ((xplus X E hM).Kl la))) with hio
  have hint : ∀ x : 𝓞 B.KO, x ≠ 0 → vV T.V (io (algebraMap (𝓞 B.KO) B.KO x)) =
      (ep (unifO (xplus X E hM) la G.N) ζ : ℤ) * vLa la (algebraMap (𝓞 B.KO) B.KO x) := by
    intro x hx
    set o : (xplus X E hM).Ol la := algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la) x with ho
    have ho0 : o ≠ 0 := by
      rw [ho, Ne, ← map_zero (algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la))]
      exact fun h => hx (FaithfulSMul.algebraMap_injective _ _ h)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 ho0)
    have hu := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))
    have hOp : IsDiscreteValuationRing.addVal (Op (xplus X E hM) la G.N) (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o) = m := by
      obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
      rw [hn, IsDiscreteValuationRing.addVal_def' u hu n] at hm
      rw [hn, map_mul, map_pow]
      have e : algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (u : (xplus X E hM).Ol la) *
          algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (unif (xplus X E hM) la) ^ n =
          ((u.isUnit.map (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N))).unit : Op (xplus X E hM) la G.N) *
            unifO (xplus X E hM) la G.N ^ n := by
        rw [IsUnit.unit_spec]; rfl
      erw [e, IsDiscreteValuationRing.addVal_def' _ (unifO_irr (E := E) (hM := hM) (G := G) (la := la)) n]
      exact hm.symm
    have e1 : io (algebraMap (𝓞 B.KO) B.KO x) = kapA h ζ T ι hι (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _
        (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o)) := by
      show kapA h ζ T ι hι (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la)) = _
      rw [show ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = algebraMap ((xplus X E hM).Ol la) ((xplus X E hM).Kl la) o from rfl,
        ← IsScalarTower.algebraMap_apply]
      rfl
    have e2 : vLa la (algebraMap (𝓞 B.KO) B.KO x) = m := by
      have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := la) (algebraMap (𝓞 B.KO) B.KO x)
      have h2 : Valued.v ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = exp (-(m : ℤ)) := valued_Ol la o m hm.symm
      unfold vLa
      rw [← h1]
      erw [h2]
      simp
    rw [e1, vV_kapA_Op h ζ T ι hι _ m hOp, e2]
    push_cast; ring
  refine ⟨ep_pos ζ h, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 B.KO) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha
  have hX : algebraMap (𝓞 B.KO) B.KO x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hx0
  have hY : algebraMap (𝓞 B.KO) B.KO y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hy0
  have hiX : io (algebraMap (𝓞 B.KO) B.KO x) ≠ 0 := (map_ne_zero io).2 hX
  have hiY : io (algebraMap (𝓞 B.KO) B.KO y) ≠ 0 := (map_ne_zero io).2 hY
  rw [map_div₀, div_eq_mul_inv, vV_mul hiX (inv_ne_zero hiY), vV_inv' hiY, hint x hx0, hint y hy0]
  have hvX : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO x) ≠ 0 := (Valuation.ne_zero_iff _).2 hX
  have hvY : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO y) ≠ 0 := (Valuation.ne_zero_iff _).2 hY
  unfold vLa
  rw [map_div₀, WithZero.log_div hvX hvY]
  ring

end Kap

section EvRp

variable {X' : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {Fd : Type} [Field Fd]
  (kap : Kp X' la N →+* Fd) (χ : X'.Forms →+* Fd)
  (hχ : ∀ (a : B.KO) (f : X'.Forms),
    χ (a • f) = kap (algebraMap (X'.Kl la) (Kp X' la N) (algebraMap B.KO (X'.Kl la) a)) * χ f)

def evRp : Rp X' la N →+* Fd :=
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : X'.Forms →ₐ[B.KO] Fd :=
    { χ with
      commutes' := fun a => by
        show χ (algebraMap B.KO X'.Forms a) = _
        rw [Algebra.algebraMap_eq_smul_one, hχ, map_one, mul_one]
        rfl }
  let vl : X'.Vl la →ₐ[X'.Kl la] Fd :=
    Algebra.TensorProduct.lift (Algebra.ofId (X'.Kl la) Fd) g (fun _ _ => Commute.all _ _)
  (Algebra.TensorProduct.lift (Algebra.ofId (Kp X' la N) Fd) vl (fun _ _ => Commute.all _ _)).toRingHom

theorem evRp_alg (k : Kp X' la N) : evRp la N kap χ hχ (algebraMap (Kp X' la N) (Rp X' la N) k) = kap k := by
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold evRp
  erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul]
  erw [map_one, mul_one]
  rfl

theorem evRp_emb (F : X'.Forms) : evRp la N kap χ hχ (emb X' la N F) = χ F := by
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd :=
    (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have e : emb X' la N F =
      ((1 : Kp X' la N) ⊗ₜ[X'.Kl la] ((1 : X'.Kl la) ⊗ₜ[B.KO] F : X'.Vl la) :
        TensorProduct (X'.Kl la) (Kp X' la N) (X'.Vl la)) := rfl
  simp only [evRp, e]
  refine (Algebra.TensorProduct.lift_tmul _ _ _ 1 _).trans ?_
  rw [map_one, one_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end EvRp

end Formalism.L2.Pj
end
end

