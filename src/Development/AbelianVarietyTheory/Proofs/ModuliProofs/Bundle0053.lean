module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KunnethSymmProductAffineCovers
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSymmOfSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Square

variable {Z : Scheme.{0}}

theorem rsT_eq {O₀ O : Z.Opens} (h : O ≤ O₀) (s : Γ(Z, O₀)) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dite_eq_left h]

theorem rsT_add {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_add _ s t
  · exact (add_zero 0).symm

theorem rsT_sub {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_sub _ s t
  · exact (sub_zero 0).symm

theorem rsT_neg {O₀ : Z.Opens} (O : Z.Opens) (s : Γ(Z, O₀)) : rsT (-s) O = -rsT s O := by
  unfold rsT
  split_ifs with h
  · exact map_neg _ s
  · exact neg_zero.symm

theorem rsT_mul {O₀ : Z.Opens} (O : Z.Opens) (s t : Γ(Z, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT
  split_ifs with h
  · exact map_mul _ s t
  · exact (mul_zero 0).symm

theorem rsT_sum {O₀ : Z.Opens} (O : Z.Opens) {g : ℕ} (s : Fin g → Γ(Z, O₀)) :
    rsT (∑ a, s a) O = ∑ a, rsT (s a) O := by
  unfold rsT
  split_ifs with h
  · exact map_sum _ s Finset.univ
  · exact Finset.sum_const_zero.symm

theorem rsT_rsT {O₀ O O' : Z.Opens} (h' : O' ≤ O) (h : O ≤ O₀) (s : Γ(Z, O₀)) :
    rsT (rsT s O) O' = rsT s O' := by
  rw [rsT_eq h', rsT_eq h, rsT_eq (h'.trans h)]
  unfold resG
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem rsT_pbT {Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O O' : Z.Opens} (h' : O' ≤ O)
    (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) : rsT (pbT f s O) O' = pbT f s O' := by
  unfold pbT
  rw [dite_eq_left h, dite_eq_left (h'.trans h), rsT_eq h']
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

variable {J : Type} {V : J → Z.Opens}

theorem iSup_inf_eq (hV : ⨆ α, V α = ⊤) (W : Z.Opens) : ⨆ α, W ⊓ V α = W := by
  rw [← inf_iSup_eq, hV, inf_top_eq]

theorem ext_cover (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (s t : Γ(Z, W))
    (h : ∀ α, rsT s (W ⊓ V α) = rsT t (W ⊓ V α)) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge s t fun α => ?_
  have hα := h α
  rw [rsT_eq inf_le_left, rsT_eq inf_le_left] at hα
  exact hα

theorem exists_glue (hV : ⨆ α, V α = ⊤) (W : Z.Opens) (F : J → ∀ O : Z.Opens, Γ(Z, O))
    (h₁ : ∀ α O, O ≤ W ⊓ V α → rsT (F α (W ⊓ V α)) O = F α O)
    (h₂ : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → F α O = F β O) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α → rsT s O = F α O := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := Z.sheaf) (U := fun α => W ⊓ V α) (V := W)
    (iUV := fun α => homOfLE inf_le_left) (iSup_inf_eq hV W).ge (fun α => F α (W ⊓ V α)) (by
      intro α β
      have e1 := h₁ α ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_left
      have e2 := h₁ β ((W ⊓ V α) ⊓ (W ⊓ V β)) inf_le_right
      have e3 := h₂ α β ((W ⊓ V α) ⊓ (W ⊓ V β)) (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      rw [rsT_eq inf_le_left] at e1
      rw [rsT_eq inf_le_right] at e2
      exact e1.trans (e3.trans e2.symm))
  refine ⟨s, fun α O hO => ?_⟩
  have hsα : resG Z (inf_le_left : W ⊓ V α ≤ W) s = F α (W ⊓ V α) := hs α
  rw [← rsT_rsT hO inf_le_left s, rsT_eq (inf_le_left : W ⊓ V α ≤ W) s, hsα]
  exact h₁ α O hO

theorem isAffineOpen_prod {S X Y : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
    (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine U := hU
  have : IsAffine W := hW
  have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
  exact IsAffine.of_isPullback
    (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl)

theorem exists_split (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (hW : IsAffineOpen W)
    (k : C1 fun α => W ⊓ V α) (hk : IsCoc _ k) :
    ∃ c : ∀ α, Γ(Z, W ⊓ V α), ∀ α β O, O ≤ W ⊓ V α ⊓ V β →
      rsT (k α β) O = rsT (c β) O - rsT (c α) O := by
  have hW' : IsAffineOpen (⨆ α, W ⊓ V α) := by
    rw [iSup_inf_eq hV W]
    exact hW
  obtain ⟨b, hb⟩ := isCob_of_isAffineOpen Z J (fun α => W ⊓ V α) k hW' hk
  refine ⟨b, fun α β O hO => ?_⟩
  have hO' : O ≤ (W ⊓ V α) ⊓ (W ⊓ V β) :=
    le_inf (hO.trans inf_le_left) (le_inf (hO.trans (inf_le_left.trans inf_le_left)) (hO.trans inf_le_right))
  rw [hb α β, rsT_sub, rsT_rsT hO' inf_le_right, rsT_rsT hO' inf_le_left]

theorem exists_compare (hV : ⨆ α, V α = ⊤) {Y : Scheme.{0}} (p : Z ⟶ Y) {T : Y.Opens}
    {W A B E : Z.Opens} (hA : W ≤ A) (hB : W ≤ B) (hE : W ≤ E) (hT : W ≤ p ⁻¹ᵁ T) {g : ℕ}
    (θ : Fin g → Γ(Y, T)) (e : Fin g → ∀ α, Γ(Z, E ⊓ V α))
    (k : C1 fun α => A ⊓ V α) (k' : C1 fun α => B ⊓ V α)
    (c : ∀ α, Γ(Z, A ⊓ V α)) (c' : ∀ α, Γ(Z, B ⊓ V α))
    (hc : ∀ α β O, O ≤ A ⊓ V α ⊓ V β → rsT (k α β) O = rsT (c β) O - rsT (c α) O)
    (hc' : ∀ α β O, O ≤ B ⊓ V α ⊓ V β → rsT (k' α β) O = rsT (c' β) O - rsT (c' α) O)
    (h : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → rsT (k' α β) O - rsT (k α β) O =
      ∑ a, pbT p (θ a) O * (rsT (e a α) O - rsT (e a β) O)) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α →
      rsT s O = rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O := by
  refine exists_glue hV W
    (fun α O => rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O)
    (fun α O hO => ?_) (fun α β O hO => ?_)
  · have hAα : W ⊓ V α ≤ A ⊓ V α := inf_le_inf_right _ hA
    have hBα : W ⊓ V α ≤ B ⊓ V α := inf_le_inf_right _ hB
    have hEα : W ⊓ V α ≤ E ⊓ V α := inf_le_inf_right _ hE
    have hTα : W ⊓ V α ≤ p ⁻¹ᵁ T := inf_le_left.trans hT
    simp only [rsT_add, rsT_sub, rsT_sum, rsT_mul, rsT_rsT hO hAα, rsT_rsT hO hBα, rsT_rsT hO hEα,
      rsT_pbT p hO hTα]
  · have h1 := hc α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hA)))
    have h2 := hc' α β O (hO.trans (inf_le_inf_right _ (inf_le_inf_right _ hB)))
    have h3 := h α β O hO
    simp only [mul_sub, Finset.sum_sub_distrib] at h3
    linear_combination h2 - h1 - h3

end GlobalTheory.KS.Square

namespace GlobalTheory.KS
open Square

theorem exists_isSymm_of_square : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (J : Type) (V : J → Z.Opens) (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j ⊓ V α)) (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ U i ⊓ V α)), ⨆ α, V α = ⊤ → (∀ i j, IsCoc _ (k i j)) → (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α → rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) → (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ V α → rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) → (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j ⊓ V α ⊓ V β → rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) → (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ⊓ V β → rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  intro K _ Y Z q p₁ p₂ I _ U g θ φ hq H hU hφ J V k e e' hV hk he he' hk₁ hk₂
  have hA : ∀ i j, IsAffineOpen (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j) := fun i j =>
    isAffineOpen_prod H (hU i) (hU j)
  choose c hc using fun i j => exists_split hV (hA i j) (k i j) (hk i j)
  choose u hu using fun i i' j => exists_compare hV p₁ (T := U i ⊓ U i')
    (W := p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ U j) (E := p₂ ⁻¹ᵁ U j)
    (inf_le_inf_right _ (p₁.preimage_mono inf_le_left)) (inf_le_inf_right _ (p₁.preimage_mono inf_le_right))
    inf_le_right inf_le_left (fun a => θ a i i') (fun a => e a j) (k i j) (k i' j) (c i j) (c i' j)
    (hc i j) (hc i' j) (hk₁ i i' j)
  choose v hv using fun i j j' => exists_compare hV p₂ (T := U j ⊓ U j')
    (W := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j') (E := p₁ ⁻¹ᵁ U i)
    (inf_le_inf_left _ (p₂.preimage_mono inf_le_left)) (inf_le_inf_left _ (p₂.preimage_mono inf_le_right))
    inf_le_left inf_le_right (fun a => θ a j j') (fun a => e' a i) (k i j) (k i j') (c i j) (c i j')
    (hc i j) (hc i j') (hk₂ i j j')
  refine _root_.GlobalTheory.KS.Kunneth.kunneth_symm K Y Z q p₁ p₂ I U g θ φ hq H hU hφ u (fun i j j' => -v i j j') ?_
  intro i i' j j'
  apply ext_cover hV
  intro α
  have hQ1 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j' :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_right)
  have hQ2 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_left)
  have hQ3 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_right)
  have hQ4 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_left)
  have hu₁ := hu i i' j' α _ (inf_le_inf_right (V α) hQ1)
  have hu₂ := hu i i' j α _ (inf_le_inf_right (V α) hQ2)
  have hv₁ := hv i' j j' α _ (inf_le_inf_right (V α) hQ3)
  have hv₂ := hv i j j' α _ (inf_le_inf_right (V α) hQ4)
  have hφ₂ := fun a => he a j j' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_right)
  have hφ₁ := fun a => he' a i i' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_left)
  have hO : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ≤
      p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := inf_le_left
  simp only [rsT_add, rsT_sub, rsT_neg, rsT_sum, rsT_mul, rsT_rsT hO hQ1, rsT_rsT hO hQ2,
    rsT_rsT hO hQ3, rsT_rsT hO hQ4, rsT_pbT p₁ hO inf_le_left, rsT_pbT p₂ hO inf_le_right]
  rw [hu₁, hu₂, hv₁, hv₂]
  simp only [← hφ₁, ← hφ₂, mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_comm (rsT (e' _ _ α) _)]
  ring

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingI
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  have h1 : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback T.hom A.hom).flip
  have h2 : IsPullback (snd T' A).left (fst T' A).left A.hom T'.hom := (IsPullback.of_hasPullback T'.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w h]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem of_parts
    (hex : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ)
    (hpb : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T T' : Over S) (h : T' ⟶ T) σ, IsAffine T.left → IsAffine T'.left → t.Emb m T σ → ∃ σ', t.Emb m T' σ' ∧ ∀ (R : Type) [CommRing R] (y : Sp R ⟶ (T' ⊗ t.A).left) (w : Ix g (N' ^ 2) → R), SecCoord _ σ' y w ↔ SecCoord _ σ (y ≫ (h ▷ t.A).left) w)
    (hspan : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk x) σ → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec t.A (σ a) : Out.SecM t.A t.L ((m : ℤ) ^ 2) (Over.mk x))) = ⊤)
    (hva : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ)
    (hfib : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th) :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ := by
  intro l1 l2 o _ g N' J b S s t m R _ x v hm h2 hth p
  have hodd : Odd N' := hth.1
  have hdvd : m ∣ N' := (dvd_pow_self m two_ne_zero).trans hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hodd.pos.ne'⟩
  obtain ⟨R', _, φ, σ, hφ, hp, hE⟩ := hex l1 l2 o g N' J b S s t m R x hodd hdvd p
  refine ⟨R', inferInstance, φ, σ, hφ, hp, hE, ?_⟩
  refine hfib R' (Ix g (N' ^ 2)) _ _ _ σ (LB.isLB_linComb t.isLB _ _) ?_ ?_
  · haveI := t.ab.proper
    exact inferInstanceAs (IsProper (pullback.fst (spMap φ ≫ x) t.A.hom))
  · intro K _ _ y
    let h : Over.mk (spMap y ≫ spMap φ ≫ x) ⟶ Over.mk (spMap φ ≫ x) := Over.homMk (spMap y) rfl
    obtain ⟨σ', hE', hc⟩ := hpb l2 o g N' J b S s t m _ _ h σ
      (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hE
    have hs := hspan l1 l2 o g N' J b S s t m K _ σ' hodd hdvd h2 hE'
    have h4 : (4 : ℤ) ≤ (m : ℤ) ^ 2 := by
      have : (2 : ℤ) ≤ m := by exact_mod_cast h2
      nlinarith
    exact ⟨_, (h ▷ t.A).left, _, _, σ', _, isPullback_whisker t.A h,
      hva l1 l2 S t.pol K _ _ _ σ' h4 hs, hc⟩

end GlobalTheory.ZM.EmbedLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodTate

theorem exists_pairing_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    [Nontrivial D.La] : ∃ a b, D.EF a b = 1 := by
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (b.coord i)
  exact ⟨a, b i, by rw [ha]; simp⟩

def rt (n : ℕ) (x : ℤ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n)) (Complex.exp_ne_zero _)

theorem rt_val (n : ℕ) (x : ℤ) : (rt n x : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / n) := rfl

theorem rt_mul (n : ℕ) (x y : ℤ) : rt n (x * y) = rt n x ^ y := by
  apply Units.ext
  rw [Units.val_zpow_eq_zpow_val, rt_val, rt_val, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem rt_congr {n : ℕ} (hn : 0 < n) {x y : ℤ} (h : (n : ℤ) ∣ x - y) : rt n x = rt n y := by
  obtain ⟨c, hc⟩ := h
  apply Units.ext
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rt_val, rt_val, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [sub_eq_iff_eq_add.1 hc]
  push_cast
  field_simp
  ring

theorem rt_pow {n m : ℕ} (hm : 0 < m) (x : ℤ) : rt (n * m) x ^ m = rt n x := by
  apply Units.ext
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Units.val_pow_eq_pow_val, rt_val, rt_val, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [← div_div, mul_div_cancel₀ _ hm']

theorem rt_prim {n : ℕ} (hn : 0 < n) {x : ℤ} (h : IsCoprime x n) : IsPrimitiveRoot (rt n x) n := by
  rw [← IsPrimitiveRoot.coe_units_iff, rt_val]
  have := Complex.isPrimitiveRoot_exp_of_isCoprime (-x) n hn.ne' h.neg_left
  convert this using 2
  push_cast
  ring

theorem pre_injective {k : Type} [Field k] (β : ℂ →+* k) (A : Over (Sp ℂ)) :
    Function.Injective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A => toUnit (Over.mk (spMap β)) ≫ x := by
  intro x y h
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  have hf : Flat (spMap β) := by
    rw [Flat.SpecMap_iff]
    letI := β.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap β) := ⟨fun p => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap β) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [Over.comp_left, e] at h'
  exact (cancel_epi (spMap β)).1 h'

theorem pre_onto (hM : Out.MulNSt) {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (Q : Out.PolAV (Sp ℂ))
    {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap β) ⟶ Q.A) (hx : x ^ n = 1) :
    ∃ y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, y ^ n = 1 ∧ toUnit _ ≫ y = x := by
  have hk : (n : k) ≠ 0 := by
    rw [← map_natCast β]
    exact (map_ne_zero β).2 (by exact_mod_cast hn.ne')
  have c₁ := (hM _ Q n hn).2.2.2.2 k (spMap β) hk
  have c₀ : Nat.card {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} = n ^ (2 * Q.g) :=
    (hM _ Q n hn).2.2.2.2 ℂ (𝟙 _) (by exact_mod_cast hn.ne')
  have : Finite {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [c₁]; positivity)
  let F : {x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A // x ^ n = 1} → {x : Over.mk (spMap β) ⟶ Q.A // x ^ n = 1} :=
    fun y => ⟨toUnit _ ≫ y.1, by
      have := map_pow (preHom (G := Q.A) (toUnit (Over.mk (spMap β)))) y.1 n
      rw [y.2, map_one] at this
      exact this.symm⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective β Q.A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁])).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (β : ℂ →+* k) (c : ℂˣ) :
    Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom (unitOn c) =
      unitOn (Units.map β.toMonoidHom c) := by
  have e : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  rw [e]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

end GlobalTheory.PeriodTate

namespace GlobalTheory


open PeriodTate in
theorem exists_tateIso_of_periods : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D'.La →+ (Fin g → ℂ)) (Q : Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) Q.A) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q.A)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), 1 ≤ D.p + D.q → IsPeriod D' ty P → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ P.range) → (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs Q.A Q.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) → (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : ℂ →+* k), ∃ I : TateIso D k (Over.mk (spMap β) ⟶ Q.A) (fun a x => x ≫ act.act a) (fun n x x' c => Out.WeilIs Q.A Q.L n x x' (unitOn c)), (∀ n : ℕ, (I.ζ n : k) = β (Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n))) ∧ ∀ (n : ℕ) a, I.ev n a = toUnit _ ≫ e ((n : ℂ)⁻¹ • P (f n a)) := by
  intro hL E _ _ _ H D D' g ty P Q act e f ν hpq hP hadd hsurj hker hact hW htow hmod hν k _ _ β
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  obtain ⟨a₀, b₀, h₀⟩ := exists_pairing_one D
  have : Nontrivial D'.La := by
    refine ⟨f 2 a₀, 0, fun h => ?_⟩
    obtain ⟨c, hc⟩ := ((hmod 2 two_pos).1 a₀).1 ⟨0, by rw [h, smul_zero]⟩
    rw [hc, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h₀
    omega
  obtain ⟨a₁, b₁, h₁⟩ := exists_pairing_one D'
  have hcong : ∀ (n : ℕ) (a b c d : D'.La), (n : ℤ) ∣ D'.EF (a + n • c) (b + n • d) - D'.EF a b := by
    intro n a b c d
    refine ⟨D'.EF a d + D'.EF c b + n * D'.EF c d, ?_⟩
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hcop : ∀ n : ℕ, 0 < n → IsCoprime (ν n) n := by
    intro n hn
    obtain ⟨a, c, ha⟩ := (hmod n hn).2 a₁
    obtain ⟨b, d, hb⟩ := (hmod n hn).2 b₁
    obtain ⟨u, hu⟩ := hcong n (f n a) (f n b) c d
    obtain ⟨v, hv⟩ := hν n hn a b
    rw [← ha, ← hb, h₁] at hu
    exact ⟨D.EF a b, u + v, by linear_combination -hu - hv⟩
  have hνt : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
    intro n m hn hm
    obtain ⟨c, hc⟩ := htow n m hn hm a₀
    obtain ⟨d, hd⟩ := htow n m hn hm b₀
    obtain ⟨u, hu⟩ := hcong n (f n a₀) (f n b₀) c d
    obtain ⟨v, hv⟩ := hν n hn a₀ b₀
    obtain ⟨w, hw⟩ := hν (n * m) (Nat.mul_pos hn hm) a₀ b₀
    rw [← hc, ← hd] at hu
    rw [h₀] at hv hw
    push_cast at hw
    exact ⟨u + v - m * w, by linear_combination hu + hv - hw⟩
  let e' : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  let ρ := preHom (G := Q.A) (toUnit (Over.mk (spMap β)))
  have hρ : Function.Injective ρ := pre_injective β Q.A
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • P (a + n • c)) = e ((n : ℂ)⁻¹ • P a) := by
    intro n hn a c
    rw [map_add (f := _), smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map β.toMonoidHom (rt n (ν n))
            ζ_prim := fun n hn => (rt_prim hn (hcop n hn)).map_of_injective (Units.map_injective β.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, rt_pow hm, rt_congr hn (hνt n m hn hm)]
            ev := fun n a => ρ (e ((n : ℂ)⁻¹ • P (f n a)))
            add := fun n a b => by rw [map_add (f := _), map_add (f := _), smul_add, hadd, map_mul]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun n => rfl, fun n a => rfl⟩
  · show toUnit (Over.mk (spMap β)) ≫ _ = (toUnit (Over.mk (spMap β)) ≫ _) ≫ _
    rw [Category.assoc, ← hact, map_smul]
    congr 2
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, hP.1, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [map_eq_one_iff ρ hρ, hker, ← (hmod n hn).1 a]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc, hsm n hn])⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := pre_onto hL.mulN β Q hn x hx
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hmod n hn).2 a'
      refine ⟨a, congrArg ρ ?_⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    rw [← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul, hsm m hm, hc, hshift n hn]
  · have h := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB (toUnit (Over.mk (spMap β)))
      (hW n (f n a) (f n b) (rt n _) hn (rt_val _ _))
    rw [unitOn_pull, rt_congr hn (hν n hn a b), rt_mul, map_zpow] at h
    exact h

end GlobalTheory
end
end

