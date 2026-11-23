module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bundle0001
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0005

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Imports
section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem c3 : SelmerFInjective := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4
    x m hx

  obtain ⟨⟨c, hc⟩, hcx⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin j)) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcx' : ∀ a, ∃ t : O, algebraMap O (FractionRing O) t = c • x a :=
    fun a => RingHom.mem_rangeS.mp (hcx a (Finset.mem_univ a))
  choose y hy using hcx'
  obtain ⟨v, rfl⟩ := hq m
  obtain ⟨d, hd0, hw'⟩ := hsat (c • v)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hw'
  have he0 : d * c ≠ 0 := mul_ne_zero hd0 hc0
  have hK0 : algebraMap O (FractionRing O) (d * c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr he0

  have cancelV : ∀ u u' : V, (d * c) • u = (d * c) • u' → u = u' := by
    intro u u' h
    rw [← algebraMap_smul (FractionRing O) (d * c) u, ← algebraMap_smul (FractionRing O) (d * c) u'] at h
    exact smul_right_injective V hK0 h
  have cancelL : ∀ a b : L, (d * c) • a = (d * c) • b → a = b := by
    intro a b h
    apply hi
    apply cancelV
    have h' := congrArg i h
    rwa [map_smul, map_smul] at h'

  have hf : ∀ g : D, ∃ zg : L, i zg = ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) := by
    intro g
    have hmem : ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_sub, hx g, hqρ]
      exact sub_self _
    rw [hker] at hmem
    exact LinearMap.mem_range.mp hmem
  choose z hz using hf
  obtain ⟨Y, hYdef⟩ : ∃ Y : coZ1s ρL, Y = ∑ a, (d * y a) • κ a - cobZ ρL w := ⟨_, rfl⟩
  have hYg : ∀ g, (Y : D → L) g = ∑ a, (d * y a) • (κ a : D → L) g - (ρL g w - w) := by
    intro g
    rw [hYdef, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]
    rfl
  have hY : ∀ g, (d * c) • z g = (Y : D → L) g := by
    intro g
    apply hi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hYg g, map_smul, hz g, map_sub, map_sub, map_sum, hiρ, hw, smul_sub, smul_sub, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, mul_smul, mul_smul, ← smul_assoc c (x a), ← hy a, algebraMap_smul]
    · rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, mul_smul, mul_smul]

  have hzc : z ∈ coZ1s ρL := by
    show ∀ g h, z (g * h) = z g + ρL g (z h)
    intro g h
    apply cancelL
    rw [smul_add, ← map_smul, hY, hY, hY]
    exact Y.2 g h
  have hZY : (d * c) • (⟨z, hzc⟩ : coZ1s ρL) = Y := Subtype.ext (funext hY)
  have hYcl : (Submodule.mkQ _ Y : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hYdef, map_sub, mkQ_cobZ, sub_zero, map_sum]
    simp only [map_smul]
  have h2 : (d * c) • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [← map_smul, hZY, hYcl]
  have hZF : (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) ∈ Ff := by
    apply hF1 (d * c) _ he0
    rw [h2]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hF2 a)
  obtain ⟨b, c', hc'0, hc'⟩ := hF3 _ hZF
  have h1 : c' • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      c' • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [smul_sub, sub_eq_zero] at hc'
    exact hc'
  have hsplit : ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) -
        (d * c) • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum]
  have h3 : c' • ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 := by
    rw [hsplit, ← h2, smul_sub, smul_comm c' (d * c), h1, smul_comm c' (d * c), sub_self]
  have hb := hF4 (fun a => d * y a - d * c * b a) c' hc'0 h3
  intro a
  have h4 : d * y a - d * c * b a = 0 := congrFun hb a
  have h5 : y a = c * b a := by
    apply mul_left_cancel₀ hd0
    rw [← mul_assoc]
    exact sub_eq_zero.mp h4
  have hc'' : algebraMap O (FractionRing O) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc0
  rw [Submodule.mem_one]
  refine ⟨b a, ?_⟩
  apply mul_left_cancel₀ hc''
  rw [← map_mul, ← h5, hy a, Algebra.smul_def]

end Formalism.RepresentationBoundsCohomology.BR
end
end

-- bundled from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LengthMapQuotLe
section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG Formalism.NG.IdempotentNormalFormsRhoFacts

lemma length_map_quot_le {O X Y : Type*} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (f : X →ₗ[O] Y) (S S' : Submodule O X) :
    Module.length O (↥(S.map f) ⧸ (S'.map f).comap (S.map f).subtype) ≤
      Module.length O (S ⧸ S'.comap S.subtype) := by
  refine Module.length_le_of_surjective
    ((S'.comap S.subtype).mapQ ((S'.map f).comap (S.map f).subtype) (f.submoduleMap S) ?_) ?_
  · intro x hx
    exact Submodule.mem_map_of_mem hx
  · intro y
    obtain ⟨y0, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := LinearMap.submoduleMap_surjective f S y0
    exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem rowRho : StatRowRho := by
  intro O _ _ _ Dw _ M _ _ ρM ε T₁ T₂ _ _ _ _ ρ₁ π γ C₁ CP Hc Cs _ _ cls pr Fs Im X
    hTate hIm hle hX hcup
  refine ⟨(annih pr Im).map Hc.subtype, Submodule.map_mono (annih_anti pr hle),
    (length_map_quot_le Hc.subtype (annih pr Im) (annih pr Fs)).trans
      (annColength O Hc Cs pr Fs Im hle), fun b hb => ?_⟩
  refine ⟨⟨_, hX b hb⟩, ?_, rfl⟩
  refine (mem_annih pr Im _).2 fun x hx => ?_
  obtain ⟨a, ha, hC, rfl⟩ := hIm x hx
  exact hTate a b (hX b hb) ha hC (hcup b hb a ha hC)

section PsiY
variable {O A T' G : Type*} [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
  {M : Type*} [AddCommGroup M] [Module A M] [Module O M] [IsScalarTower O A M]

def psiY (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) : Ymod r χ E →ₗ[O] M :=
  (φ ∘ₗ (Submodule.mkQ _) ∘ₗ (LinearMap.inl A (Ymod r χ E) _)).restrictScalars O

end PsiY

theorem rowTB : StatRowTB := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw ℓ c cB deg Hc F hFH hc hH
    htor hlen
  refine ⟨Hc ⊓ divBy F ((ℓ : O) ^ c), le_inf hFH ?_, ?_, fun φ => ⟨hH φ, ?_⟩⟩
  · intro z hz
    show ((ℓ : O) ^ c) • z ∈ F
    exact F.smul_mem _ hz
  · exact hlen.trans (mul_le_mul' (mul_le_mul' le_rfl (by exact_mod_cast hc))
      (add_le_add le_rfl one_le_two))
  · show ((ℓ : O) ^ c) • (Submodule.mkQ _ (restrictCocycles1 (uRep O (M := M) r χ) Dw
        (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) :
        H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F
    refine htor (psiY r χ E e₁ δ D j Kc k0 φ) ?_ _ (fun g => rfl)
    intro g _ y
    show φ (Submodule.Quotient.mk (uElt r χ g • y, 0)) =
      uElt r χ g • φ (Submodule.Quotient.mk (y, 0))
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Prod.smul_mk, smul_zero]

end Formalism.RepresentationBoundsCohomology.BR
end
end

-- bundled from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LiftBound
section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem colRho : StatColRho := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' tens v₁ κ
    htens he₁ hK hE hk0 hδ φ l
  obtain ⟨-, hσ, -, h4⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  choose x hx using fun a => he₁ _ (hσ a)
  have key : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) +
      (uElt r χ g • φ (nuGen r χ E e₁ δ D j Kc k0 l) - φ (nuGen r χ E e₁ δ D j Kc k0 l)) =
      (δO * (ℓ : O) ^ e' l) • ∑ a, tens (κ l a g) (x a) := by
    intro g hg
    rw [h4 g hg]
    obtain ⟨b, hb⟩ := hk0 l g
    rw [hb, mul_smul, hE, smul_zero, add_zero, hδ, mul_smul, Finset.smul_sum (r := (ℓ : O) ^ e' l)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a, ← htens, hK l a g hg, map_smul, LinearMap.smul_apply]
  refine ⟨⟨x, key⟩, fun F hF => ?_⟩
  set ρM := uRep O (M := M) r χ with hρM
  set Ψφ := colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ with hΨ
  have hz := hF (restrictCocycles1 ρM (D l) Ψφ + cobZ (resRep ρM (D l)) (φ (nuGen r χ E e₁ δ D j Kc k0 l)))
    (fun a => (δO * (ℓ : O) ^ e' l) • x a) (fun g => by
      have := key g g.2
      simp only [map_smul, ← Finset.smul_sum]
      exact this)
  rw [map_add (f := _), mkQ_cobZ, add_zero] at hz
  exact hz

theorem liftBound : StatLiftBound := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ r χ e₁ Dl j Kc ℓ e' tens v₁ κ
    htens he₁ hidem hK hinj s hs hcob a
  have hs' : ∀ a, e₁ • s a = s a := fun a => by
    obtain ⟨m, hm⟩ := hs a
    rw [← hm, DistribSMul.toLinearMap_apply, ← mul_smul, hidem]
  choose x hx using fun a => he₁ _ (hs' a)
  have h := hinj (fun a => ((ℓ : O) ^ e') • x a) (by
    convert hcob using 1
    funext g
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx a, ← htens, hK a g g.2, map_smul, map_smul, LinearMap.smul_apply]) a
  rw [hx a, ← map_smul]
  exact h

end Formalism.RepresentationBoundsCohomology.BR
end
end

-- bundled from Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.YGenCongr
section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

lemma yGen_congr {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (g g' : G)
    (hr : r g = r g') (hχ : χ g = χ g') :
    yGen r χ E e₁ δ D j Kc k0 g = yGen r χ E e₁ δ D j Kc k0 g' := by
  have hy : ycoc r χ E g = ycoc r χ E g' := by
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = ((((χ g')⁻¹ : T'ˣ) : T') • r g' - 1) * E
    rw [hr, hχ]
  unfold yGen
  congr 1
  exact Prod.ext (Subtype.ext hy) rfl

theorem qPlace : StatQPlace := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw I γ ζ ζO n hγ hquad hζ hpow
    htriv hγM
  have h1 : ∀ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M,
      (ζO - 1) • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) = 0 := by
    intro φ
    have h := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (r (γ : G) - 1) (γ : G)
      (qAlg A T' G r χ E (γ : G) ζ hquad hζ)
    have h2 := congrArg φ h
    rw [map_smul, map_zero, sub_smul, one_smul, hγM] at h2
    rw [sub_smul, one_smul]
    exact h2
  have hpw : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) (k : ℕ),
      φ (yGen r χ E e₁ δ D j Kc k0 ((γ : G) ^ k)) =
        k • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)) := by
    intro φ k
    induction k with
    | zero =>
      have h0 := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 1 ((γ : G) ^ 0) (by
        unfold ycoc
        simp)
      rw [one_smul] at h0
      rw [h0, map_zero, zero_smul]
    | succ k ih =>
      have hmem : γ ^ k ∈ I := I.pow_mem hγ k
      have ht := htriv (γ ^ k) hmem (φ (yGen r χ E e₁ δ D j Kc k0 (γ : G)))
      rw [Subgroup.coe_pow] at ht
      rw [pow_succ, yGen_mul, map_add (f := _), map_smul, ih, ht, succ_nsmul]
  refine ⟨h1, ?_⟩
  set ρD := resRep (uRep O (M := M) r χ) Dw with hρD
  set ρI := resRep ρD I with hρI
  let γ' : I := ⟨γ, hγ⟩
  let ZI : Submodule O (coZ1s ρI) :=
    { carrier := {z | (ζO - 1) • (z : I → M) γ' = 0 ∧ ∀ g : I, (z : I → M) g = n g • (z : I → M) γ'}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, fun g => ?_⟩
        · show (ζO - 1) • ((a : I → M) γ' + (b : I → M) γ') = 0
          rw [smul_add, ha1, hb1, add_zero]
        · show (a : I → M) g + (b : I → M) g = n g • ((a : I → M) γ' + (b : I → M) γ')
          rw [ha2 g, hb2 g, smul_add]
      zero_mem' := ⟨smul_zero _, fun g => (smul_zero _).symm⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        refine ⟨?_, fun g => ?_⟩
        · show (ζO - 1) • (c • (a : I → M) γ') = 0
          rw [smul_comm, ha1, smul_zero]
        · show c • (a : I → M) g = n g • (c • (a : I → M) γ')
          rw [ha2 g, smul_comm] }
  let evZ : coZ1s ρI →ₗ[O] M :=
    { toFun := fun z => (z : I → M) γ'
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : (coB1 ρI).comap (coZ1s ρI).subtype ≤ LinearMap.ker evZ := by
    rintro z ⟨v, hv⟩
    have : (z : I → M) γ' = ρI γ' v - v := (congrFun hv γ').symm
    show (z : I → M) γ' = 0
    rw [this]
    exact sub_eq_zero.mpr (htriv γ hγ v)
  let ev : H1z ρI →ₗ[O] M := Submodule.liftQ _ evZ hev
  let BI : Submodule O (H1z ρI) := ZI.map (Submodule.mkQ _)
  let B : Submodule O (H1z ρD) := BI.comap (resH1 ρD I)
  let tgt := LinearMap.ker (DistribSMul.toLinearMap O M (ζO - 1))
  have hB : ∀ b : B, ev (resH1 ρD I b) ∈ tgt := by
    rintro ⟨b, z, hz, hzb⟩
    show (ζO - 1) • ev (resH1 ρD I b) = 0
    rw [← hzb]
    exact hz.1
  let f : B →ₗ[O] tgt := LinearMap.codRestrict tgt (ev ∘ₗ resH1 ρD I ∘ₗ B.subtype) hB
  have hk1 : (unrH1 ρD I).comap B.subtype ≤ LinearMap.ker f := by
    intro b hb
    have hb' : resH1 ρD I b = 0 := hb
    refine Subtype.ext ?_
    show ev (resH1 ρD I b) = 0
    rw [hb', map_zero]
  have hk2 : LinearMap.ker f ≤ (unrH1 ρD I).comap B.subtype := by
    rintro ⟨b, z, hz, hzb⟩ hb
    have hb' : ev (resH1 ρD I b) = 0 := congrArg Subtype.val hb
    show resH1 ρD I b = 0
    rw [← hzb] at hb' ⊢
    have hz0 : (z : I → M) γ' = 0 := hb'
    have : z = 0 := Subtype.ext (funext fun g => by rw [hz.2 g, hz0, smul_zero]; rfl)
    rw [this, map_zero]
  refine ⟨B, fun x hx => ?_, ?_, fun φ => ?_⟩
  · show resH1 ρD I x ∈ BI
    rw [show resH1 ρD I x = 0 from hx]
    exact BI.zero_mem
  · refine Module.length_le_of_injective (Submodule.liftQ _ f hk1) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hk2
  · refine ⟨restrictCocycles1 ρD I (restrictCocycles1 (uRep O (M := M) r χ) Dw
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)), ⟨h1 φ, fun g => ?_⟩, rfl⟩
    show φ (yGen r χ E e₁ δ D j Kc k0 ((g : Dw) : G)) =
      n g • φ (yGen r χ E e₁ δ D j Kc k0 (γ : G))
    rw [← hpw φ (n g)]
    congr 1
    refine yGen_congr r χ E e₁ δ D j Kc k0 _ _ ?_ ?_
    · rw [(hpow g g.2).1, map_pow]
    · rw [(hpow g g.2).2, map_pow]

end Formalism.RepresentationBoundsCohomology.BR
end
end

