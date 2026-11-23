module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpMulTransport
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

namespace GlobalTheory.PolAVPull

theorem grp_mul_transport {Y X : Scheme.{0}} (G : Over X) [GrpObj G] {a b : Y ⟶ X} (h : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u'.left = u.left) (hv : v'.left = v.left) :
    (u' * v').left = (u * v).left := by
  subst h
  have e1 : u' = u := Over.OverMorphism.ext hu
  have e2 : v' = v := Over.OverMorphism.ext hv
  rw [e1, e2]

theorem polAV_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (K : Type) [Field K] (z : Sp K ⟶ X') (P₀ : PolAV (Sp K)) (θ : P₀.A.left ⟶ T.G.left), IsGrpPullback P₀.A T.G (z ≫ g) θ → LBIso P₀.L (T.PP.L.pull θ) → ∃ m : P₀.A.left ⟶ t.G.left, IsGrpPullback P₀.A t.G z m ∧ LBIso P₀.L (t.PP.L.pull m) := by
  intro E _ _ _ H X X' T t g φ K _ z P₀ θ hθ hL
  have hw : θ ≫ T.G.hom = (P₀.A.hom ≫ z) ≫ g := by rw [Category.assoc]; exact hθ.1.w
  let m : P₀.A.left ⟶ t.G.left := φ.cart.1.lift θ (P₀.A.hom ≫ z) hw
  have hm1 : m ≫ φ.φ = θ := φ.cart.1.lift_fst _ _ _
  have hm2 : m ≫ t.G.hom = P₀.A.hom ≫ z := φ.cart.1.lift_snd _ _ _
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · have s : IsPullback (m ≫ φ.φ) P₀.A.hom T.G.hom (z ≫ g) := by rw [hm1]; exact hθ.1
    exact IsPullback.of_right s hm2 φ.cart.1
  · intro T' x y x₀ y₀ hx hy
    apply φ.cart.1.hom_ext
    · let x₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (x₀.left ≫ φ.φ) (by
          show x₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w x₀]; rfl)
      let y₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (y₀.left ≫ φ.φ) (by
          show y₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w y₀]; rfl)
      have e1 := φ.cart.2 (Over.mk (T'.hom ≫ z)) x₀ y₀ x₁ y₁ rfl rfl
      let x₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (x.left ≫ θ) (by
        show x.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w x]; rfl)
      let y₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (y.left ≫ θ) (by
        show y.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w y]; rfl)
      have e2 := hθ.2 T' x y x₂ y₂ rfl rfl
      have e3 : (x₁ * y₁).left = (x₂ * y₂).left :=
        grp_mul_transport T.G (by simp [Category.assoc]) x₂ y₂ x₁ y₁
          (by simp [x₁, x₂, hx, Category.assoc, hm1]) (by simp [y₁, y₂, hy, Category.assoc, hm1])
      rw [← e1, e3, e2, Category.assoc, hm1]
    · rw [Category.assoc, hm2, Over.w]
      simp only [Over.mk_hom, ← Category.assoc, Over.w]
  · have h1 : LBIso (t.PP.L.pull m) (T.PP.L.pull θ) :=
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L m m rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame T.PP.L (fun _ : PUnit => θ) (fun _ => φ.φ) (fun _ => 1) m (fun _ => hm1.symm))
        (by obtain ⟨w, hw, -⟩ := φ.lin; exact ⟨w, hw⟩)
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.trans P₀.isLB (pull_isLB T.PP.isLB θ) (pull_isLB t.PP.isLB m) hL (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm h1)

end GlobalTheory.PolAVPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsRelatedFourierTermImages
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
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeatUniq.FourierChart

open GlobalTheory.KS GlobalTheory.Heat.Glue

theorem images_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R), (∀ a, IsField ⊤ (dd a)) → ∀ (h h' : Heat Y.H Y.q.left Q.P.L dd D), IsBasic Y h → IsBasic Y h' → ∀ (k : ℕ) (α : Q.X) (C : R), (∀ (i : h.J) (i' : h'.J) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ C * f)) → ∀ (τ₁ τ₁' τ₂ τ₂'' : SecM Y.q.left Q.P.L k), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁ (𝟙 Y.H.left) y J = sval τ₂ (𝟙 Y.H.left) y J) → (∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ₂.f fun _ => j) (Y.q.left ⁻¹ᵁ V))) → h.Acts k τ₁ τ₁' → h'.Acts k τ₂ τ₂'' → ∀ (y : Y.H.left) J, Good Q.P.L y J → sval τ₁' (𝟙 Y.H.left) y J = sval τ₂'' (𝟙 Y.H.left) y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval τ₂ (𝟙 Y.H.left) y J := by
  intro R _ _ Q Oa _ _ _ oa Y n dd D hdd h h' hb hb' k α C hloc τ₁ τ₁' τ₂ τ₂'' hgerm hwt hA hA'
  have hL : Q.P.L.IsLB := Q.P.isLB

  have e1 : ∀ c : Fin 1 → Q.P.L.ι, τ₁.f c = τ₂.f c := by
    intro c
    refine fn_ext fun x hx => ?_
    obtain ⟨J, hJ, hJc⟩ := exists_good Q.P.L hL x (fun _ : Fin 1 => 𝟙 Y.H.left ≫ Y.q.left) c
      (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => by
        simpa using Set.mem_iInter.1 hx k)
    have := hgerm x J hJ
    rwa [sval_of τ₁ (𝟙 _) x J c hJc, sval_of τ₂ (𝟙 _) x J c hJc] at this

  have loc : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (i : hh.J) (O : Y.H.left.Opens) (hO : O ≤ hh.W i)
      (f : Γ(Y.H.left, hh.W i)),
      rsT (op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k (hh.W i) f) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT f O) := by
    intro hh i O hO f
    have hd : ∀ g, resG Y.H.left hO (hh.d i (hh.W i) g) = hh.d i O (resG Y.H.left hO g) :=
      fun g => ((hh.lift i).1.2.2 (hh.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG Y.H.left hO (dd a (hh.W i) g) = dd a O (resG Y.H.left hO g) :=
      fun a g => ((hdd a).2.2 (hh.W i) O hO le_top g).symm
    have hc : ∀ r, resG Y.H.left hO (constFn Y.H.hom (hh.W i) r) = constFn Y.H.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn Y.H.hom hO r)
    have hp : ∀ p : Γ(Y.H.left, hh.W i), resG Y.H.left hO (rsT p (hh.W i)) = rsT p O := fun p => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

  have actO : ∀ (hh : Heat Y.H Y.q.left Q.P.L dd D) (τ τ' : SecM Y.q.left Q.P.L k), hh.Acts k τ τ' →
      ∀ (i : hh.J) (O : Y.H.left.Opens), O ≤ hh.W i →
      rsT (τ'.f fun _ => hh.j i) O =
        op Y.H dd hh.Θ hh.u (hh.d i) (hh.p i) (hh.p' i) k O (rsT (τ.f fun _ => hh.j i) O) := by
    intro hh τ τ' hAc i O hO
    have hW : hh.W i ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => hh.j i) := le_wchart _ (hh.le i)
    rw [← rsT_rsT hW hO (τ'.f _), hAc i, loc hh i O hO, rsT_rsT hW hO]

  have chart : ∀ (i : h.J) (i' : h'.J), ∃ O : Y.H.left.Opens, O = h.W i ⊓ h'.W i' ∧
      rsT (τ₁'.f fun _ => h'.j i') O =
        rsT (τ₂''.f fun _ => h'.j i') O + constFn Y.H.hom O C * rsT (τ₂.f fun _ => h'.j i') O := by
    intro i i'
    obtain ⟨V, hV⟩ := (hb i).1
    obtain ⟨V', hV'⟩ := (hb' i').1
    have hO : Y.q.left ⁻¹ᵁ (V ⊓ V') = h.W i ⊓ h'.W i' := by rw [hV, hV']; rfl
    refine ⟨Y.q.left ⁻¹ᵁ (V ⊓ V'), hO, ?_⟩
    have hO1 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h.W i := hO.le.trans inf_le_left
    have hO2 : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ h'.W i' := hO.le.trans inf_le_right
    have hOc : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) ⊓
        LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
      le_inf (hO1.trans (le_wchart _ (h.le i))) (hO2.trans (le_wchart _ (h'.le i')))
    have hOU : Y.q.left ⁻¹ᵁ (V ⊓ V') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h'.j i')) :=
      fun y hy => ⟨h.le i (hO1 hy), h'.le i' (hO2 hy)⟩
    have hunit : pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) *
        pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i'))⁻¹.val (Y.q.left ⁻¹ᵁ (V ⊓ V')) = 1 := by
      rw [← pbT_mul, Units.mul_inv, pbT_one _ hOU]
    have hw := hwt (h'.j i') (V ⊓ V') (hO2.trans (h'.le i'))
    have key := hloc i i' (V ⊓ V') hO.le _ hw
    have s1 := sec_rel Y.q.left k τ₁ (fun _ => h.j i) (fun _ => h'.j i') hOc
    have s1' := sec_rel Y.q.left k τ₁' (fun _ => h.j i) (fun _ => h'.j i') hOc
    have a1 := actO h τ₁ τ₁' hA i _ hO1
    have a2 := actO h' τ₂ τ₂'' hA' i' _ hO2
    beta_reduce at s1 s1'
    rw [e1, e1] at s1
    rw [e1, s1, key, ← a2, s1'] at a1
    have hu : IsUnit (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ (V ⊓ V')) ^ k) :=
      (show IsUnit _ from ⟨⟨_, _, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩).pow k
    exact hu.mul_left_cancel a1

  intro y J hJ
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h.W i by rw [h.cover]; trivial)
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, h'.W i by rw [h'.cover]; trivial)
  obtain ⟨O, hOeq, hid⟩ := chart i i'
  have hyO : y ∈ O := hOeq ▸ ⟨hi, hi'⟩
  have hOc : O ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') :=
    hOeq ▸ (inf_le_right.trans (le_wchart _ (h'.le i')))
  have hyJ := hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)
  have hyj' : (𝟙 Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h'.j i') := hOc hyO
  have tr : ∀ τ : SecM Y.q.left Q.P.L k, sval τ (𝟙 Y.H.left) y J =
      (trF (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ)) (𝟙 Y.H.left) y
        (fun _ => J (𝟙 Y.H.left ≫ Y.q.left)) (fun _ => h'.j i')).val *
        gs (𝟙 Y.H.left) y O (rsT (τ.f fun _ => h'.j i') O) := by
    intro τ
    refine (sec_trans τ (𝟙 Y.H.left) y hyJ hyj').trans (congrArg _ ?_)
    rw [rsT_of_le (show O ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U (fun _ => h'.j i') from hOc)]
    exact (gs_res (𝟙 Y.H.left) y hOc hyO _).symm
  have hc : gs (𝟙 Y.H.left) y O (constFn Y.H.hom O C) = gs (𝟙 _) y ⊤ (scal Y.H.hom C) := by
    rw [gs_constFn Y.H.hom O (𝟙 Y.H.left) y hyO C, Category.id_comp, cst, gs_eq Y.H.hom y ⊤ trivial]
    exact (gs_eq (𝟙 _) y ⊤ trivial _).symm
  rw [tr τ₁', tr τ₂'', tr τ₂, hid, gs_add _ _ _ hyO, gs_mul _ _ _ hyO, hc]
  ring

end GlobalTheory.HeatUniq.FourierChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatRingOperatorConjByPowNonzero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


open GlobalTheory.Heat in
theorem GlobalTheory.Heat.ringOp_conj_pow_gen : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  intro Ω _ _ n d δ Θ h2 u p p' c hc
  have hs : ∀ (s : Finset (Fin n)) (D : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
    intro s D x
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  refine ⟨d - ∑ a, ∑ b, ((1 / 2) * Θ a b * (δ a c / c)) • δ b - ∑ a, ∑ b, ((1 / 2) * Θ a b * (δ b c / c)) • δ a, u,
    p + d c / c - (1 / 2) * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c),
    p' - (1 / 2) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c) + ∑ a, u a * (δ a c / c), ?_, ?_⟩
  · intro y hy
    rw [Derivation.sub_apply, Derivation.sub_apply, hs, hs, Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero, sub_zero]
    · intro a _
      rw [hs]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Derivation.smul_apply, hy, smul_zero]
    · intro a _
      rw [hs]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Derivation.smul_apply, hy, smul_zero]
  · intro k f
    have e1 : ∀ b, δ b (c ^ k * f) = c ^ k * (δ b f + (k : FractionRing Ω) * (δ b c / c) * f) :=
      fun b => fractionField_derivation_pow_mul_logDeriv (δ b) hc k f
    have e2 : ∀ a b, δ a (δ b (c ^ k * f)) = c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f) := by
      intro a b
      rw [e1, fractionField_derivation_pow_mul_logDeriv (δ a) hc]
      simp only [map_add (f := _), Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
      ring
    have e3 : d (c ^ k * f) = c ^ k * (d f + (k : FractionRing Ω) * (d c / c) * f) := fractionField_derivation_pow_mul_logDeriv d hc k f
    unfold ringOp
    simp only [e2, e3]
    simp only [e1, Derivation.sub_apply, hs, Derivation.smul_apply, smul_eq_mul]
    have hL : ∑ a, ∑ b, Θ a b * (c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f)) =
        c ^ k * (∑ a, ∑ b, Θ a b * δ a (δ b f) + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
          + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
          + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c)
          + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hU : ∑ a, u a * (c ^ k * (δ a f + (k : FractionRing Ω) * (δ a c / c) * f)) =
        c ^ k * (∑ a, u a * δ a f + (k : FractionRing Ω) * f * ∑ a, u a * (δ a c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hD1 : ∑ a, ∑ b, (1 / 2) * Θ a b * (δ a c / c) * δ b f = (1 / 2) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hD2 : ∑ a, ∑ b, (1 / 2) * Θ a b * (δ b c / c) * δ a f = (1 / 2) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hh : (2 : FractionRing Ω) * (1 / 2) = 1 := mul_one_div_cancel h2
    rw [hL, hU, hD1, hD2]
    linear_combination (c ^ k * ((k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
      + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
      + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)
      + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c))) * hh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClasses
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  rw [_root_.GlobalTheory.BCT.trOn_forms_hop_eq_kernSum E hU n hn S hS lam K' hK f hf, _root_.GlobalTheory.BCT.Regroup.kernSum_eq_finsum_classes E hU n hn S hS lam K' hK f hf hreg]
  congr 1
  unfold geomURat
  refine finsum_congr fun c => ?_
  split_ifs with h
  · rw [_root_.GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb E hU n hn S hS lam K' hK f hf c.rep h]; ring
  · rfl

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofinite
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertCofinite

open Matrix TensorProduct Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem eps_dvd_nat (D : D7) (P : ℕ → Prop) (n : ℕ) (hn : n ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ n → ¬ P q) :
    ∃ t ∈ OhE D, eps D.host.E P = (n : AE D) * t := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => exact ⟨_, eps_mem P, by simp⟩
  | prime p hp =>
    obtain ⟨s, hs, e⟩ := eps_dvd (E := D.host.E) P hp (h p hp dvd_rfl) 1
    exact ⟨s, hs, by simpa using e⟩
  | mul a b ha hb =>
    obtain ⟨s, hs, es⟩ := ha (left_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_right _)
    obtain ⟨t, ht, et⟩ := hb (right_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_left _)
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    rw [← eps_idem P]
    conv_lhs => enter [1]; rw [es]
    rw [et]
    push_cast
    ring

theorem exists_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (F := ℚ) y
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, d = z := ⟨Rat.ringOfIntegersEquiv d, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  have hz : z.natAbs ≠ 0 := by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]
  have hC : levelafC (F := ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by
    rw [levelafC, map_intCast]
    exact map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z
  refine ⟨z.natAbs, Nat.pos_of_ne_zero hz, ?_⟩
  rw [hC] at hd
  rcases Int.natAbs_eq z with e | e
  · rw [e] at hd; simpa [OhE] using hd
  · rw [e] at hd
    have := neg_mem hd
    simpa [OhE] using this

theorem exists_denom_zeroAt (D : D7) (y : AE D) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D ∧ ∀ q : ℕ, q.Prime → q ∣ n → ¬ ZeroAt D q y := by
  have hex := exists_denom D y
  obtain ⟨h0, h1⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h0, h1, fun q hq hd hz => ?_⟩
  obtain ⟨m, hm, hc, s, hs, e⟩ := hz 0
  rw [pow_zero, one_mul] at e
  have hm' : (m : AE D) * y ∈ OhE D := e ▸ hs
  have hg : ((Nat.gcd (Nat.find hex) m : ℕ) : AE D) * y ∈ OhE D := by
    have := congrArg (Int.cast : ℤ → AE D) (Nat.gcd_eq_gcd_ab (Nat.find hex) m)
    push_cast at this
    rw [this]
    convert add_mem (mul_mem (intCast_mem (OhE D) (Nat.gcdA (Nat.find hex) m)) h1)
      (mul_mem (intCast_mem (OhE D) (Nat.gcdB (Nat.find hex) m)) hm') using 1
    ring
  have hle := Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left _ h0, hg⟩
  have heq : Nat.gcd (Nat.find hex) m = Nat.find hex := le_antisymm (Nat.gcd_le_left _ h0) hle
  have : q ∣ m := hd.trans (heq ▸ Nat.gcd_dvd_right _ _)
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hc.symm this

theorem intG_of_entries (D : D7) {N : ℕ} (g : GA D N)
    (h : ∀ i j, ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) :
    IntG D (g : GL (Fin N) (AE D)) := by
  have hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) := g.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hg
  intro i j
  refine ⟨h i j, ?_⟩
  rw [Units.inv_eq_of_mul_eq_one_left hg]
  exact csDual_sig_mem _ (h j i)

theorem intG_part_cofinite {D : D7} {N : ℕ} (y : GA D N) (hy : SuppInert D (y : GL (Fin N) (AE D))) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ InertQ D p) ∧
      IntG D (part D (fun p => p ∉ s) y : GL (Fin N) (AE D)) := by
  choose n h0 h1 h2 using fun ij : Fin N × Fin N => exists_denom_zeroAt D
    (((y : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2)
  refine ⟨Finset.univ.biUnion fun ij => (n ij).primeFactors, fun p hp => ?_, intG_of_entries D _ fun i j => ?_⟩
  · obtain ⟨ij, -, hp⟩ := Finset.mem_biUnion.1 hp
    have hq := Nat.prime_of_mem_primeFactors hp
    refine ⟨hq, ?_⟩
    by_contra hi
    exact h2 ij p hq (Nat.dvd_of_mem_primeFactors hp) (hy p hq hi ij.1 ij.2)
  · obtain ⟨t, ht, e⟩ := eps_dvd_nat D (fun p => p ∉ Finset.univ.biUnion fun ij => (n ij).primeFactors) (n (i, j))
      (h0 _).ne' fun q hq hd hn => hn (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Nat.mem_primeFactors.2 ⟨hq, hd, (h0 _).ne'⟩⟩)
    have := add_mem (mul_mem ht (h1 (i, j))) (one_entry_mem (OhE D) i j)
    convert this using 1
    show cutM _ _ _ i j = _
    rw [cutM_apply, e]
    ring

end GlobalTheory.InertCofinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRingMapOfPointValuesDetectFunctions
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ValInj

theorem valR_top_comp (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] (φ : R →+* Ω)
    (x' : Sp Ω ⟶ G.left) (hx : x' ≫ G.hom = spMap φ) (r : R) :
    valR x' ⊤ (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = φ r := by
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : G.left.Opens) := fun _ _ => trivial
  unfold valR
  rw [dite_eq_left ht]
  have h1 : (x'.appLE ⊤ ⊤ ht).hom (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (spMap φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← hx]
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1]
  have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.comp_apply] at h2
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h2
  exact h2

theorem injective_of_val (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (φ : R →+* Ω)
    (x' : Sp Ω ⟶ G.left) : x' ≫ G.hom = spMap φ →
    (∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → Function.Injective φ := by
  intro hx hv
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have hf := hv ⊤ _ (fun _ _ => trivial) ((valR_top_comp R G Ω φ x' hx r).trans hr)
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w (η[G])]
    rfl
  have h3 : (η[G]).left.appTop.hom (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    rfl
  rw [hf, map_zero] at h3
  have h4 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom h3
  simpa using h4.symm

end GlobalTheory.ValInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogenyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧ Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (exact GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (intros; apply GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny  <;> assumption)
end

