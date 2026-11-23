module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FinExtIn
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

def CDVRExtSt : Prop :=
  ∀ (T : CDVR), T.FinRes → ∀ (K : Type) [Field K] (jK : T.Fr →+* K),
    (letI := jK.toAlgebra; FiniteDimensional T.Fr K) →
    ∃ (T' : CDVR) (κ : K →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (κ (jK a)) = (e' : ℤ) * vV T.V a) ∧ T'.FinRes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IntFrBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (yI : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e' : ℕ), 0 < e' →
    (∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a) →
    ∃ yI' : IntFr Xo c T' (iT.comp io),
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      ∃ φ : T.Fr →ₐ[c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


variable (Xo : Moduli Dw l) (c : Coeff l) in
def BcLieAnySt : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K)
    (y : FrPt Xo c S) (τ : E →+* ℂ) (w : Sp (DualNumber K) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
    ∃! a : Fin (Dw.mult τ) → K,
      IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable {Xo : Moduli Dw l} {c : Coeff l}

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeF
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem eig_basis_of_full {x : Sp S ⟶ Xo.X} (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ i, IsTanAt x (u τ i)) (heig : ∀ τ i, IsEigAt c τ (u τ i))
    (hfull : ∀ m : TanM x Xo.univ.t.G, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S,
      m = ∑ k, a k • tvOf (hu k.1 k.2))
    (τ : E →+* ℂ) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (hwe : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w := by
  classical
  obtain ⟨a, ha, ha_uniq⟩ := hfull (tvOf hw)
  obtain ⟨α, hα, -, -⟩ := exists_sepElt c.F.val.toRingHom (fun τ => embK c τ)
    (fun τ a => rfl)
  obtain ⟨mm, hmm_def⟩ : ∃ mm : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm = fun τ' => ∑ i, a ⟨τ', i⟩ • tvOf (hu τ' i) := ⟨_, rfl⟩
  obtain ⟨mm', hmm'_def⟩ : ∃ mm' : (E →+* ℂ) → TanM x Xo.univ.t.G,
      mm' = fun τ' => if τ' = τ then tvOf hw else 0 := ⟨_, rfl⟩
  have hmm : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm τ') := by
    intro τ'
    rw [hmm_def]
    exact eig_comb τ' (fun i => tvOf (hu τ' i))
      (fun i => (eigAt_iff (c := c) (hu τ' i) τ').1 (heig τ' i)) (fun i => a ⟨τ', i⟩)
  have hmm' : ∀ τ', IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ') (mm' τ') := by
    intro τ'
    rw [hmm'_def]
    show IsEigV _ _ (if τ' = τ then tvOf hw else 0)
    by_cases h : τ' = τ
    · rw [if_pos h, h]
      exact (eigAt_iff (c := c) hw τ).1 hwe
    · rw [if_neg h]
      show ∀ b, _ = _
      intro b
      rw [map_zero, smul_zero]
  have hsum : ∑ τ', mm τ' = tvOf hw := by
    rw [hmm_def, ha, Fintype.sum_sigma]
  have hsum' : ∑ τ', mm' τ' = tvOf hw := by
    rw [hmm'_def]
    simp
  have h1 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm hmm τ
  have h2 := proj_sum_eig (ρ := actR (x0 := x) (S := S) Xo.univ.t.act) (χ := fun τ => embK c τ) (α := α)
    hα mm' hmm' τ
  rw [hsum] at h1
  rw [hsum'] at h2
  have key : tvOf hw = mm τ := by
    rw [← h1, h2, hmm'_def]
    simp
  refine ⟨fun i => a ⟨τ, i⟩, (combAt_iff (u τ) (hu τ) _ hw).2 ?_, ?_⟩
  · rw [key, hmm_def]
  · intro b hb
    rw [combAt_iff (u τ) (hu τ) b hw] at hb
    let a' : (Σ τ' : E →+* ℂ, Fin (Dw.mult τ')) → S := fun k =>
      if h : k.1 = τ then b (Fin.cast (congrArg Dw.mult h) k.2) else 0
    have ha' : tvOf hw = ∑ k, a' k • tvOf (hu k.1 k.2) := by
      rw [hb, Fintype.sum_sigma, Finset.sum_eq_single τ]
      · simp [a']
      · intro τ' _ hne
        simp [a', hne]
      · simp
    have hA := ha_uniq a' ha'
    funext i
    have hi := congrFun hA ⟨τ, i⟩
    simpa [a'] using hi

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

def NoCommonZeroSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → 4 * DF w + 4 ≤ T.Q.l.M →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom,
      ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X))
  (ε : K → ℤ) (H : Y' ⟶ Y)

theorem wchart_pull_le' (e : ∀ k, H ≫ φ k = φ' k) (j : K → L.ι) :
    (LB.LinComb L φ' ε).U j ≤ H ⁻¹ᵁ (LB.LinComb L φ ε).U j := by
  intro p hp
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : p ∈ (φ' k).base ⁻¹' (L.U (j k) : Set X) := Set.mem_iInter.1 hp k
  rw [← e k] at h1
  simpa using h1

theorem map_prod_pullU (e : ∀ k, H ≫ φ k = φ' k) (U : K → X.Opens) (u : ∀ k, Γ(X, U k)ˣ) (V : Y.Opens)
    (V' : Y'.Opens) (hV : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (hV' : ∀ k, V' ≤ φ' k ⁻¹ᵁ U k) (hH : V' ≤ H ⁻¹ᵁ V) :
    Units.map (H.appLE V V' hH).hom.toMonoidHom (∏ k, (res (hV k) (pullU (φ k) (U k) (u k))) ^ ε k) =
      ∏ k, (res (hV' k) (pullU (φ' k) (U k) (u k))) ^ ε k := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  congr 1
  ext
  show (H.appLE V V' hH).hom (((φ k).appLE (U k) V (hV k)).hom (u k : Γ(X, U k))) =
    ((φ' k).appLE (U k) V' (hV' k)).hom (u k : Γ(X, U k))
  show ((φ k).appLE (U k) V (hV k) ≫ H.appLE V V' hH).hom (u k : Γ(X, U k)) = _
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr (e k) (U k) V' _ (hV' k)]

def pullSecF (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y', (LB.LinComb L φ' ε).U j) :=
  (H.appLE ((LB.LinComb L φ ε).U j) ((LB.LinComb L φ' ε).U j) (wchart_pull_le' L φ φ' ε H e j)).hom (s.f j)

set_option maxHeartbeats 1000000 in
theorem pullSecF_compat (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (i j : K → L.ι) :
    (Y'.presheaf.map (homOfLE (inf_le_left : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
        (LB.LinComb L φ' ε).U i)).op).hom (pullSecF L φ φ' ε H e s i) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) *
        (Y'.presheaf.map (homOfLE (inf_le_right : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
          (LB.LinComb L φ' ε).U j)).op).hom (pullSecF L φ φ' ε H e s j) := by
  have hW : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
      H ⁻¹ᵁ ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) :=
    fun p hp => ⟨wchart_pull_le' L φ φ' ε H e i hp.1, wchart_pull_le' L φ φ' ε H e j hp.2⟩
  have hres : ∀ (k : K → L.ι) (hk : (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U k)
      (hk' : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤ (LB.LinComb L φ' ε).U k),
      (Y'.presheaf.map (homOfLE hk').op).hom (pullSecF L φ φ' ε H e s k) =
        (H.appLE _ _ hW).hom ((Y.presheaf.map (homOfLE hk).op).hom (s.f k)) := by
    intro k hk hk'
    show (H.appLE _ _ (wchart_pull_le' L φ φ' ε H e k) ≫ Y'.presheaf.map (homOfLE hk').op).hom (s.f k) =
      (Y.presheaf.map (homOfLE hk).op ≫ H.appLE _ _ hW).hom (s.f k)
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hu : Units.map (H.appLE _ _ hW).hom.toMonoidHom ((LB.LinComb L φ ε).g i j) = (LB.LinComb L φ' ε).g i j :=
    map_prod_pullU φ φ' ε H e (fun k => L.U (i k) ⊓ L.U (j k)) (fun k => L.g (i k) (j k)) _ _
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ' i k)) (inf_le_right.trans (LB.wchart_le L φ' j k))) hW
  have hg : (H.appLE _ _ hW).hom ((LB.LinComb L φ ε).g i j : Γ(Y, (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j)) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) :=
    congrArg Units.val hu
  rw [hres i inf_le_left inf_le_left, hres j inf_le_right inf_le_right, ← hg, ← map_mul]
  exact congrArg (H.appLE _ _ hW).hom (s.compat i j)

def pullSecLC (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) : LB.Sec (LB.LinComb L φ' ε) where
  f := pullSecF L φ φ' ε H e s
  compat := pullSecF_compat L φ φ' ε H e s

end LC

theorem exists_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S}
    (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) :
    ∃ s' : LB.Sec (LPow A L a T'), IsPullSec A L a h hh s s' := by
  have e : ∀ _k : Fin 1, h.left ≫ (snd T A).left = (snd T' A).left := fun _ => by rw [← Over.comp_left, hh]
  exact ⟨pullSecLC L _ _ _ h.left e s, fun j => rfl⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtRedPf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def WtRed : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

theorem wtRed_of (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hA : AllTest Xo c) (hW : WtField Xo c) (hB : FrBCFieldSt Xo c) : WtRed Xo c := by
  intro a n f hf S _ _ _ t y y' hb
  have hN := evNat_of Xo c hWD hA
  rw [← sub_eq_zero]
  set d := evR Xo c f y' - wchar (ex Dw a n) t * evR Xo c f y with hd
  have hP : ∀ P : Ideal S, P.IsPrime → d ∈ P := by
    intro P hPp
    have := hPp
    let ρ : S →+* FractionRing (S ⧸ P) := (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
    let _ : Algebra c.F (FractionRing (S ⧸ P)) := (ρ.comp (algebraMap c.F S)).toAlgebra
    let φ : S →ₐ[c.F] FractionRing (S ⧸ P) := { ρ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hB S y (FractionRing (S ⧸ P)) φ
    obtain ⟨z', hz'⟩ := hB S y' (FractionRing (S ⧸ P)) φ
    have hbz := frBorBC (Xo := Xo) (c := c) S (FractionRing (S ⧸ P)) φ t y y' z z' hb hz hz'
    have e1 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y z hz
    have e2 := hN f hf.1 S (FractionRing (S ⧸ P)) φ y' z' hz'
    have e3 := hW a n f hf (FractionRing (S ⧸ P)) _ z z' (hA _ z) (hA _ z') hbz
    have hw : φ (wchar (ex Dw a n) t) = wchar (ex Dw a n) (fun i => Units.map (φ : S →* FractionRing (S ⧸ P)) (t i)) := by
      simp only [wchar, map_prod, map_pow, Units.coe_map, MonoidHom.coe_coe]
    have h0 : φ d = 0 := by
      rw [hd, map_sub, map_mul, ← e1, ← e2, e3, hw, sub_self]
    have h1 : algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P d) = 0 := h0
    have h2 : Ideal.Quotient.mk P d = 0 :=
      (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))) (by rw [h1, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hnil : d ∈ nilradical S := by
    rw [nilradical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun Q hQ => hP Q hQ
  exact IsReduced.eq_zero d (mem_nilradical.mp hnil)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

