module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.QzSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cycRange :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (cycZ L Ω l).range = KStar.TotallyRealRoots.princ l (cZero l L) := by
  intro L Ω _ _ _ _ _ l _ hq
  have hmu := muQ L Ω l
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsGalois L Ω := inferInstance
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hinj := (algebraMap L Ω).injective
  have key : ∀ (σ : G L Ω) (n : ℕ) (t : Ω), t ^ l ^ n = 1 →
      σ t = t ^ ((cycZ L Ω l σ : ℤ_[l]).toZModPow n).val := by
    intro σ n t ht
    exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G L Ω) Ω σ) t ht
  have hmem : ∀ (a : ℕ) (u : ℤ_[l]ˣ), u ∈ KStar.TotallyRealRoots.princ l a ↔ (u : ℤ_[l]).toZModPow a = 1 := by
    intro a u
    simp [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff]
  have hone : ∀ (n : ℕ) (t : Ω), IsPrimitiveRoot t (l ^ n) → t ^ ((1 : ZMod (l ^ n)).val) = t := by
    intro n t ht
    rw [ZMod.val_one_eq_one_mod, ht.eq_orderOf, pow_mod_orderOf, pow_one]
  have hfixed : ∀ (n : ℕ) (t : Ω) (a : ZMod (l ^ n)), IsPrimitiveRoot t (l ^ n) → t ^ a.val = t → a = 1 := by
    intro n t a ht h
    apply ZMod.val_injective
    apply ht.pow_inj (ZMod.val_lt a) (ZMod.val_lt 1)
    rw [h, hone n t ht]
  have hq' : qExp l ≤ cZero l L := hmu.2.2.1.mp hq
  have hle : (cycZ L Ω l).range ≤ KStar.TotallyRealRoots.princ l (cZero l L) := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨ζ, hζ⟩ := (hmu.1 (cZero l L)).2 le_rfl
    have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ cZero l L) := hζ.map_of_injective hinj
    have hfix : σ (algebraMap L Ω ζ) = algebraMap L Ω ζ := σ.commutes ζ
    rw [key σ _ _ hζ'.pow_eq_one] at hfix
    exact (hmem _ _).2 (hfixed _ _ _ hζ' hfix)
  apply le_antisymm hle
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (cZero l L + 1))
  have hnot : ξ ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨x, rfl⟩
    have hx : IsPrimitiveRoot x (l ^ (cZero l L + 1)) := hξ.of_map_of_injective hinj
    have := (hmu.1 (cZero l L + 1)).1 ⟨x, hx⟩
    omega
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed] at hnot
  push_neg at hnot
  obtain ⟨σ, hσ⟩ := hnot
  have hu : cycZ L Ω l σ ∈ KStar.TotallyRealRoots.princ l (cZero l L) := hle ⟨σ, rfl⟩
  have hu' : cycZ L Ω l σ ∉ KStar.TotallyRealRoots.princ l (cZero l L + 1) := by
    intro hm
    apply hσ
    rw [key σ _ _ hξ.pow_eq_one, (hmem _ _).1 hm, hone _ _ hξ]
  have hgen := ((princGen l (cZero l L) hq').1 _ hu).2 hu'
  refine hgen.trans (Subgroup.topologicalClosure_minimal _ ?_ ?_)
  · rw [Subgroup.zpowers_le]
    exact ⟨σ, rfl⟩
  · rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_cycZ L Ω l)).isClosed
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenGal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.genGal :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], IsClosed (galOf k L Ω : Set (G k Ω)) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤) ∧
        (Procyc L Ω l → ∃ γ, IsGen l (galOf k L Ω) γ) := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hcl : IsClosed (galOf k L Ω : Set (G k Ω)) :=
    Subgroup.isClosed_of_isOpen _ (galEmbTop k L Ω).2.1
  have hχ : ∀ g : G L Ω, cycZ k Ω l (galEmb k L Ω g) = cycZ L Ω l g := fun g =>
    DFunLike.congr_fun (galEmbFam k L Ω l).2.2.1 g
  have hiff : Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤ := by
    by_cases h : l = 2
    · subst h
      refine or_congr_right ?_
      rw [← range_galEmb]
      constructor
      · rintro h _ ⟨g, rfl⟩
        refine ⟨trivial, ?_⟩
        show cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2
        rw [hχ]
        exact h g
      · intro h g
        have h' : cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2 := (h ⟨g, rfl⟩).2
        rw [hχ] at h'
        exact h'
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  exact ⟨hcl, hiff, fun h => UpperTheory.V.Tower.existsGen k Ω l _ hcl (hiff.1 h)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LenDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem le_dual (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] :
    Module.length ℤ_[l] N ≤ Module.length ℤ_[l] (N →ₗ[ℤ_[l]] QZ l) := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length, ← Order.krullDim_orderDual]
  refine Order.krullDim_le_of_strictMono
    (fun p : (Submodule ℤ_[l] N)ᵒᵈ =>
      LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (OrderDual.ofDual p).subtype)) ?_
  intro a b hab
  change OrderDual.ofDual b < OrderDual.ofDual a at hab
  obtain ⟨hle, m, hmp, hmq⟩ := SetLike.lt_iff_le_and_exists.mp hab
  refine lt_of_le_of_ne ?_ ?_
  · intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    ext ⟨x, hx⟩
    have h := LinearMap.congr_fun hφ ⟨x, hle hx⟩
    simpa using h
  · intro heq
    have hm0 : (OrderDual.ofDual b).mkQ m ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := qzSep l _ _ hm0
    have hmem : ψ ∘ₗ (OrderDual.ofDual b).mkQ ∈
        LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (OrderDual.ofDual b).subtype) := by
      rw [LinearMap.mem_ker]
      ext ⟨x, hx⟩
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx]
    have hmem' := hmem
    simp only at heq
    rw [← heq, LinearMap.mem_ker] at hmem'
    exact hψ (by simpa using LinearMap.congr_fun hmem' ⟨m, hmp⟩)

private theorem exact_dual (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N] [Module ℤ_[l] N]
    (p : Submodule ℤ_[l] N) :
    Function.Exact (LinearMap.lcomp ℤ_[l] (QZ l) p.mkQ) (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  rw [LinearMap.exact_iff]
  have h := (dualKer l N (N ⧸ p) p.mkQ).1
  have hq := Submodule.ker_mkQ p
  generalize LinearMap.ker p.mkQ = q at h hq
  subst hq
  exact h.symm

private theorem simple_dual (l : ℕ) [hl : Fact l.Prime]
    (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [hN : IsSimpleModule ℤ_[l] N] :
    IsSimpleModule ℤ_[l] (N →ₗ[ℤ_[l]] QZ l) := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial ℤ_[l] N
  have hnu : (l : ℤ_[l]) ∈ nonunits ℤ_[l] :=
    (IsLocalRing.mem_maximalIdeal _).mp
      (by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)
  have hspan : ∀ s : N, s ≠ 0 → ∀ x : N, ∃ c : ℤ_[l], c • s = x := by
    intro s hs x
    have htop : Submodule.span ℤ_[l] {s} = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by simpa [Submodule.span_singleton_eq_bot] using hs)
    exact Submodule.mem_span_singleton.mp (htop ▸ Submodule.mem_top)
  have hkill : ∀ s : N, (l : ℤ_[l]) • s = 0 := by
    intro s
    by_contra h
    obtain ⟨c, hc⟩ := hspan _ h s
    have hu : IsUnit (1 - c * (l : ℤ_[l])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mul_mem_nonunits_right hnu)
    have h0 : (1 - c * (l : ℤ_[l])) • s = 0 := by
      rw [sub_smul, one_smul, mul_smul, hc, sub_self]
    have hs0 : s = 0 := (hu.smul_eq_zero).mp h0
    exact h (by rw [hs0, smul_zero])
  obtain ⟨s, hs⟩ := exists_ne (0 : N)
  obtain ⟨φ0, hφ0⟩ := qzSep l N s hs
  obtain ⟨ι, hιinj, hιrange, hιsmul⟩ := zmodToQZ l 1
  haveI : Fact (Nat.Prime (l ^ 1)) := ⟨by rw [pow_one]; exact hl.out⟩
  have hrange : ∀ φ : N →ₗ[ℤ_[l]] QZ l, ∃ a, ι a = φ s := by
    intro φ
    refine (hιrange (φ s)).mpr ?_
    rw [pow_one, ← LinearMap.map_smul_of_tower, hkill, map_zero]
  have key : ∀ φ ψ : N →ₗ[ℤ_[l]] QZ l, φ ≠ 0 → ∃ z : ℤ_[l], ψ = z • φ := by
    intro φ ψ hφ
    have hφs : φ s ≠ 0 := by
      intro h
      apply hφ
      ext x
      obtain ⟨c, rfl⟩ := hspan s hs x
      simp [h]
    obtain ⟨a, ha⟩ := hrange φ
    obtain ⟨b, hb⟩ := hrange ψ
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hφs (by rw [← ha, map_zero])
    obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (b * a⁻¹)
    have hb' : b = PadicInt.toZModPow 1 (k : ℤ_[l]) * a := by
      rw [map_natCast, hk, inv_mul_cancel_right₀ ha0]
    refine ⟨(k : ℤ_[l]), ?_⟩
    ext x
    obtain ⟨c, rfl⟩ := hspan s hs x
    rw [map_smul, LinearMap.smul_apply, map_smul, ← hb, ← ha, hb', hιsmul, smul_comm]
  haveI : Nontrivial (N →ₗ[ℤ_[l]] QZ l) := ⟨⟨φ0, 0, fun h => hφ0 (by rw [h]; rfl)⟩⟩
  refine { eq_bot_or_eq_top := fun P => ?_ }
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    obtain ⟨φ, hφP, hφ0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    rw [eq_top_iff]
    intro ψ _
    obtain ⟨z, rfl⟩ := key φ ψ hφ0'
    exact P.smul_mem z hφP

theorem UpperTheory.V.Tower.lenDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M], Module.length ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) = Module.length ℤ_[l] M := by
  intro l _ M _ _
  by_cases hM : IsFiniteLength ℤ_[l] M
  · induction hM with
    | @of_subsingleton M' _ _ _ =>
      haveI : Subsingleton (M' →ₗ[ℤ_[l]] QZ l) :=
        ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      simp [Module.length_eq_zero]
    | @of_simple_quotient M' _ _ N _ _ ih =>
      have hS := simple_dual l (M' ⧸ N)
      have e1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
        N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      have e2 := Module.length_eq_add_of_exact (LinearMap.lcomp ℤ_[l] (QZ l) N.mkQ)
        (LinearMap.lcomp ℤ_[l] (QZ l) N.subtype)
        (fun f g h => by
          ext x
          exact LinearMap.congr_fun h x)
        ((dualKer l M' M' (LinearMap.id)).2 N) (exact_dual l N)
      rw [e1, e2, ih, Module.length_eq_one (R := ℤ_[l]) (M := M' ⧸ N),
        Module.length_eq_one (R := ℤ_[l]) (M := (M' ⧸ N) →ₗ[ℤ_[l]] QZ l), add_comm]
  · have h1 : Module.length ℤ_[l] M = ⊤ := by
      rw [← not_ne_iff, Module.length_ne_top_iff]
      exact hM
    have h2 := le_dual l M
    rw [h1, top_le_iff] at h2
    rw [h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ShaDGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.shaDGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U V : Subgroup (G k Ω)) [U.Normal] (e : ℤ) (γ : G k Ω), IsClosed (U : Set (G k Ω)) → V ≤ U → IsGen l V γ →
        ShaD l N U V e = LinearMap.ker (dTw l N U e γ - 1) ∧ ShaD l N U V e = LinearMap.ker (dTw l N U e γ⁻¹ - 1) := by
  intro k Ω _ _ _ _ _ l hl N U V _ e γ hU hVU hγ
  have key : ∀ φ : Dinf l N U, dTw l N U e γ φ = φ → ∀ v ∈ V, dTw l N U e v φ = φ := by
    intro φ hφ v hv
    obtain ⟨n, hn⟩ := (dinfNil k Ω l N U hU φ.1 φ.2).1
    obtain ⟨r, hr⟩ := (dinfTors k Ω l N U).1 hU φ
    have hlev : ∀ w ∈ U, cycZ k Ω l w ∈ KStar.TotallyRealRoots.princ l (max n r) → dTw l N U e w φ = φ := by
      intro w hw hc
      have h1 : dRep l N U w φ = φ :=
        Subtype.ext (hn w ⟨hw, KStar.TotallyRealRoots.princ_anti (le_max_left n r) hc⟩)
      have h2 : cycZ k Ω l w ^ (-e) ∈ KStar.TotallyRealRoots.princ l r :=
        Subgroup.zpow_mem _ (KStar.TotallyRealRoots.princ_anti (le_max_right n r) hc) _
      rw [KStar.TotallyRealRoots.mem_princ] at h2
      obtain ⟨c, hc'⟩ := h2
      rw [dTw_apply, LinearMap.smul_apply, h1, sub_eq_iff_eq_add.1 hc', add_smul, one_smul, mul_comm, mul_smul, hr,
        smul_zero, zero_add]
    have hz : ∀ j : ℤ, dTw l N U e (γ ^ j) φ = φ := by
      intro j
      let S : Subgroup (G k Ω) :=
        { carrier := {g | dTw l N U e g φ = φ}
          mul_mem' := fun {a b} ha hb => by
            show dTw l N U e (a * b) φ = φ
            rw [map_mul, Module.End.mul_apply, show dTw l N U e b φ = φ from hb]; exact ha
          one_mem' := by
            show dTw l N U e 1 φ = φ
            rw [map_one]; rfl
          inv_mem' := fun {a} ha => by
            show dTw l N U e a⁻¹ φ = φ
            conv_lhs => rw [← show dTw l N U e a φ = φ from ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
      exact S.zpow_mem (show γ ∈ S from hφ) j
    have hcl : cycZ k Ω l v ∈ closure ((Subgroup.zpowers (cycZ k Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
      hγ.2 ⟨v, hv, rfl⟩
    have hop : IsOpen ((fun x : ℤ_[l]ˣ => x⁻¹ * cycZ k Ω l v) ⁻¹' (KStar.TotallyRealRoots.princ l (max n r) : Set ℤ_[l]ˣ)) :=
      (KStar.TotallyRealRoots.isOpen_princ _).preimage (by fun_prop)
    obtain ⟨x, hx, j, rfl⟩ := mem_closure_iff.1 hcl _ hop (by simp [one_mem])
    have h3 := hlev ((γ ^ j)⁻¹ * v) (U.mul_mem (U.inv_mem (U.zpow_mem (hVU hγ.1) j)) (hVU hv))
      (by rw [map_mul, map_inv, map_zpow]; exact hx)
    have h4 : v = γ ^ j * ((γ ^ j)⁻¹ * v) := by group
    rw [h4, map_mul, Module.End.mul_apply, h3, hz]
  constructor
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    exact ⟨fun h => h ⟨γ, hγ.1⟩, fun h v => key φ h v.1 v.2⟩
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    refine ⟨fun h => h ⟨γ⁻¹, V.inv_mem hγ.1⟩, fun h v => key φ ?_ v.1 v.2⟩
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
end

