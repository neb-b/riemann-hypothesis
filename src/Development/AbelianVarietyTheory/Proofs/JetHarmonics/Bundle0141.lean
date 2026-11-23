module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundFromCharactersPointDatumStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_bound_from_characters_pointDatum : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  first | exact @GlobalTheory.DepthFromChars.depth_bound_of_chars | exact GlobalTheory.DepthFromChars.depth_bound_of_chars | (intros; apply GlobalTheory.DepthFromChars.depth_bound_of_chars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_inv_entry (k r : ℕ) (c j : Fin (2 * r + k + 1)) :
    B.CkOn ⊤ (B.GV k r) (fun y : B.Mat k r => y⁻¹ c j) := by
  intro g₀ _
  refine ⟨Set.univ, fun g => Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c g, isOpen_univ, trivial,
    (Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c).contDiff.contDiffOn, fun g _ hg => ?_⟩
  show g⁻¹ c j = Matrix.mulVec (Hpk k r * g.conjTranspose * Hpk k r) (Pi.single j 1) c
  rw [← Formalism.FourierDecayAlt.P.JCx2.mn_inv_gv hg]
  simp

theorem inCC_inv_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (c j : Fin (2 * r + k + 1)) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A m F) :
    B.InCC (A - 1) m (fun g : B.Mat k r => g⁻¹ c j • F g) := by
  have hg : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => g⁻¹ c j) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_congr (fun g _ => by simp)
      (Formalism.FourierDecayAlt.P.JCx2.pd_good_inv (Wp := Wp) (Wq := Wq) (Pi.single j 1) c)
  obtain ⟨K, -, hK⟩ := hg.2 (A - 1) m
  obtain ⟨b, hb⟩ := hF
  exact ⟨K * b, hK F b (by rw [Nat.cast_one, sub_add_cancel]; exact hb)⟩

theorem inv_entry_smul_eigen_split : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  intro k r Wp Wq _ _ _ _ _ _ lam A i j f hlam hf heig
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hE, hE', hι, hq, hsm, hext, hcc, hex, -, hqC, hmul⟩ :=
    GlobalTheory.capelli_module_model k r Wp Wq lam A
  obtain ⟨w, hw⟩ := hex f hf heig
  let x : Fin (2 * r + k + 1) → Module.End ℂ V := fun c => mul (fun y : B.Mat k r => y⁻¹ c j)
  have hx : ∀ c v, ∀ g ∈ B.GV k r, ev (x c v) g = g⁻¹ c j • ev v g :=
    fun c => (hmul _ (ckOn_inv_entry k r c j)).1
  have hcomm : ∀ a b c, E a b * x c = x c * E a b - if a = c then x b else 0 := by
    intro a b c
    ext v
    refine hext _ _ fun g hg => ?_
    have h1 := (hmul _ (ckOn_inv_entry k r c j)).2 a b v g hg
    rw [GlobalTheory.eh_inv_entry k r a b c j g hg] at h1
    rw [Module.End.mul_apply, LinearMap.sub_apply, map_sub, Pi.sub_apply, Module.End.mul_apply, hx _ _ g hg]
    refine h1.trans ?_
    split_ifs with h
    · rw [hx _ _ g hg, neg_smul, sub_eq_add_neg]
    · simp
  have hinj : Function.Injective
      (fun s => ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2)) := by
    intro s t h
    apply hlam
    have h' : (lam s : ℂ) = lam t := sub_left_inj.1 h
    exact_mod_cast h'
  obtain ⟨v, hv1, hv2⟩ := GlobalTheory.covector_multiplier_shift V W _ E E' ι x _ hE hE' hι hinj hq hcomm i w
  refine ⟨fun t => ev (∑ a, x a (ι (v t a))), fun t => ⟨hsm _, fun m => ?_⟩, fun t Y g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum (A := A - 1) (m := m) Finset.univ
      (fun a (g : B.Mat k r) => g⁻¹ a j • ev (ι (v t a)) g)
      (fun a _ => inCC_inv_entry_smul a j (hcc (v t a) m))
    refine ⟨b, Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => ?_) hb⟩
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hx _ _ g hg).symm
  · rw [← hqC _ _ g hg, hv2, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun s _ => ?_
    split_ifs <;> push_cast <;> ring
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← hw g hg, ← hx i _ g hg, hv1, map_sum, Finset.sum_apply]

end GlobalTheory
end

