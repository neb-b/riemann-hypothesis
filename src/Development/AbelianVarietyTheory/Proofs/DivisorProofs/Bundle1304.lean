module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalConjToSquareInertPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomial
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.ShiftMono

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

theorem mulW_comm (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [G.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  ring

theorem shift_comm (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · show G.mulW 0 u (shift G v x 0) = G.mulW 0 v (shift G u x 0)
    rw [shift_apply_zero, shift_apply_zero, map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext k
  rcases k with _ | k
  · rw [shift_apply_zero, Pi.single_eq_of_ne (by omega)]
  · rw [shift_apply_succ]
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (by omega), map_zero]

variable (s : Fin G.D → Fin G.N → F)

def mono (α : Fin G.D →₀ ℕ) {j l : ℕ} (h : j + α.degree = l) : G.Sec j →ₗ[F] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) (⟨α, rfl⟩ : MonoDeg (Fin G.D) α.degree)
    ((Nat.cast_add j _).symm.trans (congrArg _ h))

theorem mono_add (α β γ : Fin G.D →₀ ℕ) (e : γ = α + β) {j l' l : ℕ} (h : j + γ.degree = l)
    (h₂ : j + β.degree = l') (h₁ : l' + α.degree = l) (m : G.Sec j) :
    mono G s γ h m = mono G s α h₁ (mono G s β h₂ m) := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_add]
  ring

theorem mono_zero (α : Fin G.D →₀ ℕ) (e : α = 0) {j : ℕ} (h : j + α.degree = j) (m : G.Sec j) :
    mono G s α h m = m := by
  subst e
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_zero, one_mul]

theorem mono_single (i : Fin G.D) {j : ℕ} (h : j + (Finsupp.single i 1).degree = j + 1) (m : G.Sec j) :
    mono G s (Finsupp.single i 1) h m = G.mulW j (s i) m := by
  rw [G.mulW_apply]
  unfold mono
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulSec _ _ _ _ _ _ _ _ _ hc hk]
  simp only [monoVal_single, pow_one]

def Acts (E : Module.End F (Tot G)) (α : Fin G.D →₀ ℕ) : Prop :=
  ∀ (j l : ℕ) (h : j + α.degree = l) (m : G.Sec j), E (Pi.single j m) = Pi.single l (mono G s α h m)

theorem acts_one : Acts G s 1 0 := fun j l h m => by
  obtain rfl : j = l := by simpa using h
  rw [mono_zero G s 0 rfl h m]; rfl

theorem acts_mul {E₁ E₂ : Module.End F (Tot G)} {α₁ α₂ : Fin G.D →₀ ℕ} (h₁ : Acts G s E₁ α₁) (h₂ : Acts G s E₂ α₂) :
    Acts G s (E₁ * E₂) (α₁ + α₂) := fun j l h m => by
  have h' : j + α₂.degree + α₁.degree = l := by rw [map_add (f := _)] at h; omega
  rw [Module.End.mul_apply, h₂ j (j + α₂.degree) rfl m, h₁ (j + α₂.degree) l h',
    ← mono_add G s α₁ α₂ (α₁ + α₂) rfl]

theorem acts_shift (i : Fin G.D) : Acts G s (shift G (s i)) (Finsupp.single i 1) := fun j l h m => by
  obtain rfl : l = j + 1 := by simpa using h.symm
  rw [shift_single, mono_single]

theorem acts_pow (i : Fin G.D) (k : ℕ) : Acts G s (shift G (s i) ^ k) (Finsupp.single i k) := by
  induction k with
  | zero => simpa using acts_one G s
  | succ k ih =>
    rw [pow_succ, show Finsupp.single i (k + 1) = Finsupp.single i k + Finsupp.single i 1 by simp]
    exact acts_mul G s ih (acts_shift G s i)

theorem acts_list : ∀ (n : ℕ) (E : Fin n → Module.End F (Tot G)) (g : Fin n → Fin G.D →₀ ℕ),
    (∀ i, Acts G s (E i) (g i)) → Acts G s (List.ofFn E).prod (∑ i, g i)
  | 0, E, g, _ => by simpa using acts_one G s
  | n + 1, E, g, hE => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact acts_mul G s (hE 0) (acts_list n _ _ fun i => hE i.succ)

theorem acts_pw (α : Fin G.D →₀ ℕ) : Acts G s (HSShort.pw (shift G) s α) α := by
  have := acts_list G s G.D (fun i => shift G (s i) ^ α i) (fun i => Finsupp.single i (α i))
    fun i => acts_pow G s i (α i)
  rwa [Finsupp.univ_sum_single] at this

end GlobalTheory.HSShort.ShiftMono

namespace GlobalTheory.HSShort

theorem shift_comm_single_mono : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F),
    (∀ u v, shift G u * shift G v = shift G v * shift G u) ∧ (∀ (j : ℕ) u (m : G.Sec j), shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m)) ∧ ∀ (s : Fin G.D → Fin G.N → F) (a j l : ℕ) (h : j + a = l) (α : MonoDeg (Fin G.D) a) (m : G.Sec j), pw (shift G) s α.1 (Pi.single j m) = Pi.single l (mulPow G s h α m) := by
  intro F _ _ G
  refine ⟨ShiftMono.shift_comm G, ShiftMono.shift_single G, fun s a j l h α m => ?_⟩
  obtain ⟨α, rfl⟩ := α
  exact ShiftMono.acts_pw G s α j l h m

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExists
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem exists_basis_fin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] : ∃ N, Nonempty (Module.Basis (Fin N) A B) := by
  by_cases hA : Nontrivial A
  · exact ⟨_, ⟨Module.finBasis A B⟩⟩
  · rw [not_nontrivial_iff_subsingleton] at hA
    have : Subsingleton B := Module.subsingleton A B
    exact ⟨0, ⟨Module.Basis.empty B⟩⟩

theorem hilbertScheme_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ _ _ r
  obtain ⟨N, ⟨e⟩⟩ := exists_basis_fin A B
  let F := GlobalTheory.HilbAff.functor A B r
  choose X x hX hlft hbas huniv using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  choose W hW _ using fun (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : F.obj (op Z)) =>
    GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ Z y
  have stab : ∀ σ (Z : Scheme.{0}) (g : Z ⟶ X σ), GlobalTheory.HilbAff.Basic A B e σ (F.map g.op (x σ)) := by
    intro σ Z g
    have htop : Set.range (𝟙 (X σ)) ⊆ (W σ (X σ) (x σ) : Set (X σ)) :=
      (hW σ _ _ _ (𝟙 _)).2 (by rw [op_id, F.map_id]; exact hbas σ)
    exact (hW σ _ _ _ g).1 (fun z _ => htop ⟨z, rfl⟩)
  have hrep : F.IsRepresentable := by
    refine GlobalTheory.GeneratorFunctor.isRepresentable_of_charts F (GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski A B r) X x W ?_ ?_ ?_
    · intro σ Z y Z' a
      rw [hW]
      constructor
      · intro hb
        obtain ⟨g, hg, -⟩ := huniv σ Z' _ hb
        exact ⟨g, hg⟩
      · rintro ⟨g, hg⟩
        rw [← hg]
        exact stab σ Z' g
    · intro σ Z g g' h
      obtain ⟨g₀, -, hu⟩ := huniv σ Z _ (stab σ Z g)
      exact (hu g rfl).trans (hu g' h.symm).symm
    · intro Z y z
      obtain ⟨σ, U, hz, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e Z y z
      refine ⟨σ, (hW σ Z y U U.ι).2 hb ?_⟩
      simpa using hz
  let R := F.representableBy
  obtain ⟨U, u, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.affineHilbert_representing_universal_subscheme A B r F.reprX R
  obtain ⟨q1, q2, q3⟩ := GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType A B r F.reprX R
  refine ⟨F.reprX, (R.homEquiv (𝟙 _)).1, U, u, ?_, h1, h2, h3, h4, h5⟩
  rw [IsProper.eq_valuativeCriterion, ValuativeCriterion.eq]
  exact ⟨⟨⟨⟨GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence A B r F.reprX R, _root_.GlobalTheory.HilbAff.valuativeCriterion_uniqueness A B r F.reprX R⟩, q1⟩, q2⟩, q3⟩

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviPlaneSection

open Matrix

section Alg

variable {S : Type*} [CommRing S] {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}

end Alg

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E]

end Forms


end GlobalTheory.LeviPlaneSection

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialStabilizerTransferConjSelfDualLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TransferHyp

theorem stab_iff_entries {R : Type} [CommRing R] {n : ℕ} (O : Subring R) {X Y : Matrix (Fin n) (Fin n) R}
    (hXY : X * Y = 1) (hYX : Y * X = 1) :
    (∀ z : Fin n → R, (∀ i, z i ∈ O) ↔ ∀ i, X.mulVec z i ∈ O) ↔ (∀ i j, X i j ∈ O) ∧ ∀ i j, Y i j ∈ O := by
  have hs : ∀ j i : Fin n, (Pi.single j 1 : Fin n → R) i ∈ O := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hm : ∀ {A : Matrix (Fin n) (Fin n) R}, (∀ i j, A i j ∈ O) → ∀ z : Fin n → R, (∀ i, z i ∈ O) →
      ∀ i, A.mulVec z i ∈ O := fun {A} hA z hz i => by
    change ∑ j, A i j * z j ∈ O
    exact sum_mem fun j _ => mul_mem (hA i j) (hz j)
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using (h _).1 (hs j) i
    · have := (h (Y.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]
        exact hs j) i
      simpa using this
  · rintro ⟨h1, h2⟩ z
    refine ⟨hm h1 z, fun hz => ?_⟩
    have := hm h2 _ hz
    rwa [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] at this

theorem stab_conj {R : Type} [CommRing R] {n : ℕ} (I Λ : (Fin n → R) → Prop) {A B H G X : Matrix (Fin n) (Fin n) R}
    (hAB : A * B = 1) (hBA : B * A = 1) (hHG : H * G = 1)
    (hΛ : ∀ y, Λ y ↔ I (B.mulVec (H.mulVec y))) :
    (∀ y, Λ y ↔ Λ ((G * (A * X * B) * H).mulVec y)) ↔ ∀ z, I z ↔ I (X.mulVec z) := by
  have key : ∀ y, B.mulVec (H.mulVec ((G * (A * X * B) * H).mulVec y)) = X.mulVec (B.mulVec (H.mulVec y)) := fun y => by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    calc B * (H * (G * (A * X * B) * H)) = B * (H * G) * A * X * (B * H) := by simp only [Matrix.mul_assoc]
      _ = X * (B * H) := by rw [hHG, Matrix.mul_one, hBA, Matrix.one_mul]
  simp only [hΛ, key]
  refine ⟨fun h z => ?_, fun h y => h _⟩
  have e : B.mulVec (H.mulVec (G.mulVec (A.mulVec z))) = z := by
    rw [Matrix.mulVec_mulVec _ H, hHG, Matrix.one_mulVec, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  have := h (G.mulVec (A.mulVec z))
  rwa [e] at this

theorem finMat_mul {D : D7} (V : HSp D) (g h : GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h :=
  congrArg Units.val (map_mul (finHom V) g h)

theorem finMat_one {D : D7} (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 :=
  congrArg Units.val (map_one (finHom V))

def finComp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Ad E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
  (GlobalTheory.LFun.finAdEquiv F E).symm.toRingHom.comp (pFin E)

def intRing (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
  ⨅ u : HeightOneSpectrum (𝓞 E), (Ov E u).comap (GlobalTheory.LFun.compAt F u)

theorem mem_intRing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) : z ∈ intRing F E ↔ ∀ u, GlobalTheory.LFun.compAt F u z ∈ Ov E u := by
  simp only [intRing, Subring.mem_iInf, Subring.mem_comap]

theorem stab_finComp_iff (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMField E] {n : ℕ} (x : UA E n) :
    (∀ z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E, (∀ i, z i ∈ intRing F E) ↔
      ∀ i, (x.1.1.map (finComp F E)).mulVec z i ∈ intRing F E) ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  have hκ : ∀ (y : UA E n) a b, (y.1.1.map (finComp F E)) a b ∈ intRing F E ↔
      ∀ u, (cLoc u y).1 a b ∈ u.adicCompletionIntegers E := fun y a b => by
    refine (mem_intRing _).trans (forall_congr' fun u => ?_)
    have e : GlobalTheory.LFun.compAt F u ((y.1.1.map (finComp F E)) a b) = (cLoc u y).1 a b :=
      congrArg (fun t => pLoc E u t) ((GlobalTheory.LFun.finAdEquiv F E).apply_symm_apply (pFin E (y.1.1 a b)))
    rw [e]
    exact Iff.rfl
  have hXY : ∀ y : UA E n, y.1.1.map (finComp F E) * (y⁻¹).1.1.map (finComp F E) = 1 := fun y => by
    rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX := hXY x⁻¹
  rw [inv_inv] at hYX
  refine (stab_iff_entries _ (hXY x) hYX).trans ?_
  simp only [hκ]

theorem mem_KGL_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {x : UA E n} (hx : x ∈ locU n P) : cLoc P x ∈ GlobalTheory.LFun.KGL P (n := n) ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  constructor
  · intro h2
    exact ⟨fun a b u => GlobalTheory.UnramDict.cLoc_entry_mem hx h2 u a b, fun a b u =>
      GlobalTheory.UnramDict.cLoc_entry_mem (inv_mem hx) (by rw [map_inv]; exact inv_mem h2) u a b⟩
  · rintro ⟨h4, h5⟩
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun a b => h4 a b P, fun a b => ?_⟩
    rw [← map_inv]
    exact h5 a b P

theorem map_mul_map_inv {K R : Type} [Field K] [CommRing R] {n : ℕ} (ι : K →+* R) {M N : Matrix (Fin n) (Fin n) K}
    (h : N * M = 1) : M.map ι * M⁻¹.map ι = 1 ∧ M⁻¹.map ι * M.map ι = 1 := by
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse h
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]

theorem cj_mem_hyp_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P := by
  intro D _ V j h₀ M hM _ _ hj hlat hloc P x
  have hO : ∀ z, z ∈ intAE D ↔ z ∈ intRing D.host.F D.host.E := fun z =>
    (GlobalTheory.LFun.mem_intAE_iff_compAt z).trans (mem_intRing z).symm
  obtain ⟨hAB, hBA⟩ := map_mul_map_inv (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E).toRingHom hM
  have hHG : finMat D.sp.cm.sig V.gram h₀ * finMat D.sp.cm.sig V.gram h₀⁻¹ = 1 := by
    rw [← finMat_mul, mul_inv_cancel, finMat_one]
  have hst : (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram (cj j h₀ x)).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ↔
      (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers D.host.E) ∧
        ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers D.host.E := by
    rw [cj_apply, finMat_mul, finMat_mul, hj]
    exact (stab_conj (fun z => ∀ i, z i ∈ intRing D.host.F D.host.E)
      (fun y => y ∈ latHat D.host.F D.host.E (L0c D V)) hAB hBA hHG
      fun y => (hlat y).trans (forall_congr' fun i => hO _)).trans (stab_finComp_iff D.host.F x)
  constructor
  · rintro ⟨⟨h1, h2, -⟩, e, f, hef, h3⟩
    have hx := (hloc P e f hef x).2 ⟨h1, h3⟩
    exact ⟨hx, (mem_KGL_iff hx).2 (hst.1 h2)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e, f, hef⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.LFun.comp_finAdEquiv D) P
    obtain ⟨h3, h4⟩ := (hloc P e f hef x).1 h1
    exact ⟨⟨h3, hst.2 ((mem_KGL_iff h1).1 h2), fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, hef, h4⟩

end GlobalTheory.TransferHyp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
section
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Fin

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsIndMap (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (A : P →ₗ[ℂ] (UA σ W.J → P₁)) : Prop where
  right : ∀ g ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (om (1, g)) φ φ₁ → ∀ h ∈ UAt σ W (evFin F v), A (p φ₁) h = A (p φ) (h * g)
  unip : ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x (u * h) = A x h
  levi : ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) →
    h₁ ∈ UAt σ W₁ (evFin F v) → ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v),
    Acts (evFin F v) (om₁ (1, h₁)) φ φ₁ → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = p₁ φ →
      A x (m * h) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ φ₁

def IndLineFin (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) : Prop :=
  ∀ A A' : P →ₗ[ℂ] (UA σ W.J → P₁), IsIndMap v om om₁ p p₁ H' χ z A → IsIndMap v om om₁ p p₁ H' χ z A' →
    (∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = 0) ∨ ∃ c : ℂ, ∀ x, ∀ h ∈ UAt σ W (evFin F v), A' x h = c • A x h

end Fin

section Inf

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsFrobInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (φ : P →ₗ[ℂ] P₁) : Prop where
  unip : ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → φ (p f₁) = 0
  lie : ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
    ActsD (evI F) (fun s => om₁ (1, γ₁ (Multiplicative.ofAdd s))) g g₁ → φ (p f) = p₁ g → ∀ c : ℂ,
    HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
      (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 →
      φ (p f₁) = p₁ g₁ + c • φ (p f)
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ (t : (AE F E)ˣ) (k₁ : UA σ W₁.J), IsLevi H' t k₁ k → k₁ ∈ KInf σ W₁ B.emb →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁), Acts (evI F) (om₁ (1, k₁)) g g₁ → φ (p f) = p₁ g →
      φ (p f₁) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ g₁

def IndLineInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) : Prop :=
  ∀ φ φ' : P →ₗ[ℂ] P₁, IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ → IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ' →
    φ = 0 ∨ ∃ c : ℂ, φ' = c • φ

end Inf

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnipotentRadicalConjToSquareInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  first | exact @GlobalTheory.InertConjSq.conj_sq | exact GlobalTheory.InertConjSq.conj_sq | (intros; apply GlobalTheory.InertConjSq.conj_sq <;> assumption)
end

