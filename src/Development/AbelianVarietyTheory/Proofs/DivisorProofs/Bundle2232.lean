module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.FibreDim

theorem charZero_residueField_genericPoint' (X : Scheme.{0}) [IsIntegral X] (hc : CharZero Γ(X, ⊤)) :
    CharZero (X.residueField (genericPoint X)) := by
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X _ _
  have hr : Function.Injective (X.residue (genericPoint X)) := (X.residue (genericPoint X)).hom.injective
  exact charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ X.residue _).hom)
    (by simpa using hr.comp hg)

theorem not_charZero_residueField {Z : Scheme.{0}} (p : ℕ) [Fact p.Prime] (s : Z ⟶ Sp (ZMod p)) (z : Z) :
    ¬ CharZero (Z.residueField z) := by
  intro hc
  let φ : ZMod p →+* Z.residueField z :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫ s.appTop ≫ Z.Γevaluation z).hom
  have h0 : ((p : ZMod p) : ZMod p) = 0 := ZMod.natCast_self p
  have : (p : Z.residueField z) = 0 := by rw [← map_natCast φ p, h0, map_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

end GlobalTheory.FibreDim

namespace GlobalTheory.FibreDim

theorem fibre_isProjOver_and_dim_le : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (X := (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  intro k _ W q hq p _
  haveI hgc : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  refine ⟨?_, ?_⟩
  · letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    exact VertProj.isProjOver_strHom_zmod k W q 1 hq _
      (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) p
  · set f := q ≫ spMap (Int.castRingHom k)
    set g := spMap (Int.castRingHom (ZMod p))
    have := hq.isIntegral
    have hemb := (pullback.fst f g).isClosedEmbedding
    have hs : IsClosed (Set.range (pullback.fst f g)) := hemb.isClosed_range
    have hne : ∀ z, (pullback.fst f g) z ≠ genericPoint W := by
      intro z hz
      have h1 := charZero_residueField_genericPoint' W hq.charZero
      rw [← hz] at h1
      exact not_charZero_residueField p (pullback.snd f g) z
        (charZero_of_injective_ringHom ((pullback.fst f g).residueFieldMap z).hom.injective)
    have key := topologicalKrullDim_add_one_le hs isClosed_univ (T := W) fun x hx =>
      ⟨genericPoint W, trivial, fun ⟨z, hz⟩ => hne z hz, genericPoint_specializes x⟩
    have hW : topologicalKrullDim (Set.univ : Set W) ≤ 2 := by
      have := topologicalKrullDim_subspace_le W Set.univ
      rw [hq.dim_eq] at this
      exact this
    have heq : topologicalKrullDim (Set.range (pullback.fst f g)) =
        topologicalKrullDim ↥(pullback (C := Scheme.{0}) f g) :=
      GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
    rw [← heq]
    have h2 := key.trans hW
    generalize topologicalKrullDim (Set.range (pullback.fst f g)) = d at h2 ⊢
    induction d with
    | bot => exact bot_le
    | coe n =>
      norm_cast at h2 ⊢
      induction n with
      | top => exact absurd h2 (by decide)
      | coe m =>
        norm_cast at h2 ⊢
        have h3 : m + 1 ≤ 2 := by exact_mod_cast h2
        omega

end GlobalTheory.FibreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactor
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvSmall

theorem fullRk_irred : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), GlobalTheory.FullRankCoinv.augRk n d ν ≤ N →
      N ≤ GlobalTheory.FullRankCoinv.fullRk k n d → (∀ h : GL (Fin d) k, ∀ Ψ ∈ N, (fun Y => Ψ (Y * h.1)) ∈ N) →
      N = GlobalTheory.FullRankCoinv.augRk n d ν ∨ N = GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := _root_.GlobalTheory.FullRankCoinv.fibre_coinvariants k n d ν hnd hs
  rcases _root_.GlobalTheory.FullRankCoinv.indSp_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by
    rintro _ ⟨Ψ, hΨ, rfl⟩ h₀; exact ⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE
  · left
    refine le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA
    have : Z Ψ ∈ N.map Z := ⟨Ψ, hΨ, rfl⟩
    rw [hE] at this
    exact (Submodule.mem_bot ℂ).1 this
  · right
    refine le_antisymm hNF (fun Ψ hΨ => ?_)
    have : Z Ψ ∈ N.map Z := hE ▸ hZ1 Ψ hΨ
    obtain ⟨Ψ', hΨ', he⟩ := this
    have h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν :=
      hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])
    have := N.add_mem hΨ' (hA h1)
    rwa [add_sub_cancel] at this

theorem irr_small : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν N hAN hNS hN
  obtain ⟨t, ι, ν₀, hs, hu, hbij, hso, hg, hh⟩ := _root_.GlobalTheory.WeilTransfer.transfer hP F E σ B a a' G X om om' hT v hv
  have hR := _root_.GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt hP F E σ B a a' G X om om' hT v hv hν t
  have haugSB : augAt om' v ≤ SB _ := Submodule.span_le.2 (by
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ)

  have hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤
      (augAt om' v).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ.1
    obtain ⟨g, hgU, hg'⟩ := hg g₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hg' φ hφ
    refine ⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩
    · rw [← he]
      exact Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1
    · intro Y hY
      rw [← he]
      show ι φ₁ Y - ι φ Y = 0
      rw [he, hΨ.2 Y hY]
      simp only [GlobalTheory.FullRankCoinv.lact, sub_zero]
      rw [hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
        rw [Matrix.det_transpose]; exact (Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]
  set N' := N.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') with hN'
  have hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N' :=
    hgen.trans (inf_le_inf_right _ (Submodule.map_mono hAN))
  have hst : ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N' := by
    rintro h₀ _ ⟨⟨φ, hφN, rfl⟩, hΨ⟩
    obtain ⟨h, hhU, c, hc, hh'⟩ := hh h₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hh' φ (hNS hφN)
    have h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁ := by
      rw [he]; funext Y; simp [hc]
    refine ⟨⟨c⁻¹ • φ₁, N.smul_mem _ (hN h hhU φ hφN φ₁ hφ₁ hA), by rw [map_smul, h1]⟩, ?_, ?_⟩
    · rw [h1]; exact Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)
    · intro Y hY
      exact hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])
  have hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι φ = ι φ' → φ = φ' := fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e
  have hloc : ∀ φ₀ ∈ G.M'.SoLoc B.ψ t, ι φ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') :=
    fun φ₀ h0 => ⟨hbij.mapsTo h0.1, (hso φ₀ h0.1).1 h0⟩
  rcases fullRk_irred hP (Fv F v) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE
  · left
    refine le_antisymm (fun φ hφN => ?_) hAN
    obtain ⟨φ₀, h0, hd⟩ := hR φ (hNS hφN)
    have h0N : φ₀ ∈ N := by
      have := N.sub_mem hφN (hAN hd); rwa [sub_sub_cancel] at this
    have h1 : ι φ₀ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ := hE ▸ ⟨⟨φ₀, h0N, rfl⟩, hloc φ₀ h0⟩
    obtain ⟨⟨w, hw, hwe⟩, -⟩ := hgen h1
    have : w = φ₀ := hinj w (haugSB hw) φ₀ h0.1 hwe
    subst this
    have := (augAt om' v).add_mem hw hd
    rwa [add_sub_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφ => ?_)
    obtain ⟨φ₀, h0, hd⟩ := hR φ hφ
    have h1 : ι φ₀ ∈ N' := hE ▸ hloc φ₀ h0
    obtain ⟨⟨φ', hφ'N, he⟩, -⟩ := h1
    have : φ' = φ₀ := hinj φ' (hNS hφ'N) φ₀ h0.1 he
    subst this
    have := N.add_mem hφ'N (hAN hd)
    rwa [add_sub_cancel] at this

end GlobalTheory.IrrCoinvSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AxisTriv

theorem lift_comp_sq {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare β β₂) (a b : B ⟶ B) (a' b' : A ⟶ A)
    (ha : a.left ≫ β = β ≫ a'.left) (hb : b.left ≫ β = β ≫ b'.left) :
    (lift a b).left ≫ β₂ = β ≫ (lift a' b').left := by
  have k₁ : (lift a b).left ≫ (fst B B).left = a.left := congrArg (fun z => z.left) (lift_fst a b)
  have k₂ : (lift a' b').left ≫ (fst A A).left = a'.left := congrArg (fun z => z.left) (lift_fst a' b')
  have l₁ : (lift a b).left ≫ (snd B B).left = b.left := congrArg (fun z => z.left) (lift_snd a b)
  have l₂ : (lift a' b').left ≫ (snd A A).left = b'.left := congrArg (fun z => z.left) (lift_snd a' b')
  apply pullback.hom_ext
  · change ((lift a b).left ≫ β₂) ≫ (fst A A).left = (β ≫ (lift a' b').left) ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, k₁, Category.assoc, k₂, ha]
  · change ((lift a b).left ≫ β₂) ≫ (snd A A).left = (β ≫ (lift a' b').left) ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, l₁, Category.assoc, l₂, hb]

theorem exists_gen_pull {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} (hP : P.IsLB) (a : B ⟶ B ⊗ B) (a' : A ⟶ A ⊗ A)
    (e : a.left ≫ β₂ = β ≫ a'.left) (h : ∃ u : (P.pull a'.left).Gen, u.IsGen) :
    ∃ u : ((P.pull β₂).pull a.left).Gen, u.IsGen := by
  obtain ⟨u, hu⟩ := h
  have i₁ : LBIso ((P.pull β₂).pull a.left) (P.pull (a.left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (LB.isLB_pull hP β₂)) a.left
  have i₂ : LBIso ((P.pull a'.left).pull β) (P.pull (β ≫ a'.left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (LB.isLB_pull hP a'.left)) β
  rw [e] at i₁
  have i := LBIso.trans (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull hP _) (LB.isLB_pull (LB.isLB_pull hP _) _) i₁ i₂.symm
  obtain ⟨w, hw⟩ := i.symm
  obtain ⟨v, hv, -⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_pull (LB.isLB_pull hP _) _) (LB.isLB_pull (LB.isLB_pull hP _) _)
    w hw (pullGenLB u β) (pullGenLB_isGen hu β)
  exact ⟨v, hv⟩

theorem axes_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left), P.IsLB → (∃ u : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, u.IsGen) → ∀ (t : T ⟶ S) (B : Over T) [GrpObj B] (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsGrpPullback B A t β → IsSquare β β₂ → (∃ u : ((P.pull β₂).pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) ∧ (∃ u : ((P.pull β₂).pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) := by
  intro S T A _ P hP h₁ h₂ t B _ β β₂ h hs
  have e₁ := GlobalTheory.PPAS.one_comp_of_isGrpPullback h
  exact ⟨exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ e₁ rfl) h₁,
    exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ rfl e₁) h₂⟩

end GlobalTheory.AxisTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeOfHyp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianBaseChange

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}

theorem isPull1_unique {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    {w : φ ≫ s = s' ≫ spMap (algebraMap R R')} (hu : Function.Injective (pullHyp1 (pairRes φ s')))
    {c : HH1 s} {c₁ c₂ : HH1 s'} (h₁ : IsPull1 w c c₁) (h₂ : IsPull1 w c c₂) : c₁ = c₂ :=
  hu (h₁.symm.trans h₂)

theorem core (s₀ s : X ⟶ Sp R) (hs : s = s₀) (s₀' s' : X' ⟶ Sp R') (hs' : s' = s₀') (φ : X' ⟶ X)
    (hpb : φ ≫ s₀ = s₀' ≫ spMap (algebraMap R R'))
    (m : IsMor (dp0 R) s (dp0 R') s' (algebraMap R R') φ)
    (hcmp : Function.Bijective (cmp1 s)) (hcmp' : Function.Bijective (cmp1 s'))
    (hO : Function.Injective (cmpO s)) (hu : Function.Injective (pullHyp1 (pairRes φ s')))
    (hcl : ClosedForm s₀ = ⊤) (hcl' : ClosedForm s₀' = ⊤)
    (e : R' ⊗[R] HH1 s₀ ≃ₗ[R'] HH1 s₀') (he : ∀ c, IsPull1 hpb c (e (1 ⊗ₜ c)))
    (e' : R' ⊗[R] GlobForm s₀ ≃ₗ[R'] GlobForm s₀') (he' : ∀ c, IsPullForm hpb c (e' (1 ⊗ₜ c))) :
    Function.Bijective (liftSemi m.pull1) ∧
      F1 s' = Submodule.span R' (m.pull1 '' (F1 s : Set (FirstDeRham s))) := by
  subst hs hs'

  have key : ∀ c : FirstDeRham s, cmp1 s' (m.pull1 c) = e (1 ⊗ₜ cmp1 s c) := fun c ↦
    isPull1_unique hu (comparison_pullback m c) (he _)
  let C := LinearEquiv.ofBijective (cmp1 s) hcmp
  let C' := LinearEquiv.ofBijective (cmp1 s') hcmp'
  have hsq : (cmp1 s') ∘ₗ liftSemi m.pull1 =
      e.toLinearMap ∘ₗ (LinearEquiv.baseChange R R' _ _ C).toLinearMap := by
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul x c =>
      simp only [LinearMap.coe_comp, Function.comp_apply, liftSemi_tmul, map_smul,
        LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, key]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  refine ⟨?_, ?_⟩
  · have hb : Function.Bijective ((cmp1 s') ∘ liftSemi m.pull1) := by
      have := congrArg DFunLike.coe hsq
      rw [LinearMap.coe_comp] at this
      rw [this, LinearMap.coe_comp]
      exact (e.bijective).comp (LinearEquiv.baseChange R R' _ _ C).bijective
    exact (Function.Bijective.of_comp_iff' hcmp' _).1 hb
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · intro c' hc'
      have h1 : cmp1 s' c' ∈ CechHodgeFiltration s' := comparison_mem_cechHodgeFiltration s' hc'
      rw [cechHodgeFiltration_eq_range] at h1
      obtain ⟨ω', hω'⟩ := h1
      let Φ : GlobForm s' →ₗ[R'] HH1 s' :=
        clForm s' ∘ₗ (LinearEquiv.ofTop _ hcl').symm.toLinearMap
      let Ψ : R' ⊗[R] GlobForm s →ₗ[R'] FirstDeRham s' := C'.symm.toLinearMap ∘ₗ Φ ∘ₗ e'.toLinearMap
      have hΦ : ∀ ω : ClosedForm s', Φ ω.1 = clForm s' ω := fun ω ↦ by
        simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.ofTop_symm_apply]
      obtain ⟨z, hz⟩ := e'.surjective ω'.1
      have hc'z : c' = Ψ z := by
        apply hcmp'.1
        simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hz, hΦ]
        rw [← hω']
        exact (C'.apply_symm_apply _).symm
      rw [hc'z]
      clear hc'z hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | tmul x ω =>
        rw [show x ⊗ₜ[R] ω = x • (1 ⊗ₜ[R] ω) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          map_smul]
        refine Submodule.smul_mem _ x (Submodule.subset_span ?_)
        let ωc : ClosedForm s := ⟨ω, hcl ▸ trivial⟩
        refine ⟨C.symm (clForm s ωc), ?_, ?_⟩
        · have hF : clForm s ωc ∈ CechHodgeFiltration s := by rw [cechHodgeFiltration_eq_range]; exact ⟨ωc, rfl⟩
          change toH1O s _ = 0
          apply hO
          rw [← structureSheaf_comparison_comm, map_zero]
          have : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc := C.apply_symm_apply _
          rw [this]
          exact hF
        · apply hcmp'.1
          let ωc' : ClosedForm s' := ⟨e' (1 ⊗ₜ ω), hcl' ▸ trivial⟩
          have h2 : IsPull1 hpb (clForm s ωc) (clForm s' ωc') := IsPullForm.cl (he' ω)
          have h3 := comparison_pullback m (C.symm (clForm s ωc))
          have h4 : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc := C.apply_symm_apply _
          rw [h4] at h3
          rw [isPull1_unique hu h3 h2]
          simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
          rw [hΦ ωc']
          exact (C'.apply_symm_apply _).symm
    · rintro _ ⟨c, hc, rfl⟩
      exact m.pullback1_mem_hodgeFiltration hc

end GlobalTheory.AbelianBaseChange

namespace GlobalTheory.AbelianBaseChange

theorem abelianDeRham_baseChange_of_smoothLift (H₁ : GlobalTheory.Published.CrystallineSmoothLift) (H₂ : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro R _ A _ g hA hg R' _ _ A' _ φ h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h.1 hg
  have hF := GlobalTheory.AbelianPrim.abelianDeRham_free (_root_.GlobalTheory.Proof.abelianDeRhamFree_of_hodge H₁ H₂)
  have hP : primDR A = ⊤ := (hF R A g hA hg).1
  have hP' : primDR A' = ⊤ := (hF R' A' g hA' hg').1
  have geom : ∀ {S : Type} [CommRing S] (B : Over (Sp S)) [GrpObj B], IsAbelianScheme B →
      Smooth (B.hom ≫ 𝟙 _) ∧ IsSeparated (B.hom ≫ 𝟙 _) ∧ QuasiCompact (B.hom ≫ 𝟙 _) := by
    intro S _ B _ hB
    rw [Category.comp_id]
    haveI := hB.smooth
    haveI := hB.proper
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨sm, se, sq⟩ := geom A hA
  obtain ⟨sm', se', sq'⟩ := geom A' hA'
  have hcmp := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R A.left (A.hom ≫ 𝟙 _) sm se sq).1
  have hcmp' := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R' A'.left (A'.hom ≫ 𝟙 _) sm' se' sq').1
  obtain ⟨-, -, -, -, ⟨hcl, -, -⟩, hbc⟩ := H₂ R A g hA hg
  obtain ⟨-, -, -, -, ⟨hcl', -, -⟩, -⟩ := H₂ R' A' g hA' hg'
  obtain ⟨⟨e, he⟩, ⟨e', he'⟩, -⟩ := hbc R' A'.left A'.hom φ h.1
  let m := (GlobalTheory.Published.AbelianDeRham.bcMor h).isMor
  obtain ⟨hB, hF1⟩ := core A.hom (A.hom ≫ 𝟙 _) (Category.comp_id _) A'.hom (A'.hom ≫ 𝟙 _)
    (Category.comp_id _) φ h.1.w m hcmp hcmp' (_root_.GlobalTheory.CechDR.cmpO_injective R A.left _)
    (_root_.GlobalTheory.CechDR.pairRes_injective φ (A'.hom ≫ 𝟙 _)).2.2 hcl hcl' e he e' he'
  refine ⟨?_, ?_⟩
  · have hsq : (LinearEquiv.ofTop _ hP').toLinearMap ∘ₗ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull =
        liftSemi m.pull1 ∘ₗ (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).toLinearMap := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul x c => rfl
    have hb : Function.Bijective
        ((LinearEquiv.ofTop _ hP') ∘ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull) := by
      have := congrArg DFunLike.coe hsq
      rw [LinearMap.coe_comp] at this
      rw [LinearEquiv.coe_toLinearMap] at this
      rw [this, LinearMap.coe_comp]
      exact hB.comp (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).bijective
    exact (Function.Bijective.of_comp_iff' (LinearEquiv.ofTop _ hP').bijective _).1 hb
  · apply Submodule.map_injective_of_injective (primDR A').injective_subtype
    rw [PrimitiveSubmodule, Submodule.map_comap_eq, Submodule.range_subtype,
      inf_eq_right.2 (by rw [hP']; exact le_top), hF1,
      Submodule.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, by rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hP]; trivial⟩, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.1, hc, rfl⟩

end GlobalTheory.AbelianBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalPrimeDivisorOrdersFunctionsTopForms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

namespace GlobalTheory.BirOrd

theorem ord_and_formOrd_of_over : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), DivOver.Over s E' E →
      (∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (ratPull p s n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro X Y _ _ p _ n _ s _ hbij E E' hO
  exact ⟨DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbij E' E hO,
    fun η hη => formOrd_ratPull_of_over ℂ X Y p s hbij E' E hO n η hη⟩

end GlobalTheory.BirOrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmulStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt),
      PtExt.IsCan t c x → PtExt.IsCan t c' x' → PtExt.IsCan t (c + c') (x + x')) ∧
    ∀ (r : R) (c : primDR A) (x : G.RigExt), PtExt.IsCan t c x → PtExt.IsCan t (r • c) (r • x) :=
  PtExt.isCan_add_smul R A p G t
end

