module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigSign

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0LocalCardBoundedOfClsKerLeKer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.H0_local_card_bounded_of_cls_ker_le_ker :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → (cls ℚ Ω N).ker ≤ ψ.ker →
          (∀ (A : ValuationSubring Ω) (U : Subgroup (G ℚ Ω)), A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ U →
            h0 l e ψ U ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O) ∧ h0 l e ψ ⊤ ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O := by
  intro Ω _ _ _ l hl O _ _ _ _ _ N _ e ψ he hψ
  have key : ∀ (A : ValuationSubring Ω) (U : Subgroup (G ℚ Ω)), A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ U →
      h0 l e ψ U ≤ (LDataCardLeFinrank.nuBound l N e : ℕ∞) * eO l O := by
    intro A U hA hU
    have h1 := (h0Nu ℚ Ω l O e ψ U).1 (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker) (inf_le_left.trans hU)
    have h2 := (h0Nu ℚ Ω l O e ψ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker)).2 (inf_le_right.trans hψ)
    have h3 := LDataCardLeFinrank.nuLeBound l N e _ ((clsOnto Ω N).2 l A hA) he
    exact h1.trans (h2.trans (mul_le_mul_left h3 _))
  obtain ⟨A, hA⟩ := (placesQ Ω).1 l hl.out
  exact ⟨key, key A ⊤ hA le_top⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem lift_gens {Γ Q : Type} [Group Γ] [Group Q] (p : Γ →* Q) (hp : Function.Surjective p)
    (T : Finset Q) (hT : Subgroup.closure (T : Set Q) = ⊤) :
    ∃ T' : Finset Γ, T'.card ≤ T.card ∧ ⊤ ≤ Subgroup.closure (T' : Set Γ) ⊔ p.ker := by
  classical
  choose s hs using hp
  refine ⟨T.image s, Finset.card_image_le, ?_⟩
  rw [← Subgroup.comap_map_eq, MonoidHom.map_closure, Finset.coe_image, Set.image_image]
  simp only [hs, Set.image_id', hT, Subgroup.comap_top, le_refl]

theorem UpperTheory.V.Chr.upV :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure L Ω] [IsAbelianGalois k L]
          (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (D : LData L Ω l) (e : ℕ) (ψ : G k Ω →* Oˣ), galOf k L Ω ≤ ψ.ker →
          ∀ T : Finset (L ≃ₐ[k] L), Subgroup.closure (T : Set (L ≃ₐ[k] L)) = ⊤ →
          V l e ψ ≤ shaLen D (e : ℤ) * eO l O + (T.card : ℕ∞) * h0 l e ψ ⊤ := by
  intro k Ω _ _ _ _ _ L _ _ _ _ _ _ _ l _ O _ _ _ _ _ D e ψ hψ T hT
  obtain ⟨hp, hker, -⟩ := galQuot k L Ω
  obtain ⟨T', hc, hT'⟩ := lift_gens _ hp T hT
  have hab : ∀ a ∈ (⊤ : Subgroup (G k Ω)), ∀ b ∈ (⊤ : Subgroup (G k Ω)), a * b * a⁻¹ * b⁻¹ ∈ galOf k L Ω := by
    intro a _ b _
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm' (AlgEquiv.restrictNormalHom L a)]
    simp
  rw [hker] at hT'
  have hopen : IsOpen ((ψ⁻¹ : G k Ω →* Oˣ).ker : Set (G k Ω)) :=
    Subgroup.isOpen_mono (H₁ := galOf k L Ω) (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.inv_apply, MonoidHom.mem_ker.1 (hψ hg), inv_one]) (galEmbTop k L Ω).2.1
  have hk := kerResAb O (G k Ω) (QO l O) (rho l e ψ) ((contTw k Ω l).2.2 O _ _ hopen) (qoFacts l O).1
    (fun g => ⟨_, fun m => scalRep_apply _ _ g m⟩) (galOf k L Ω) ⊤ le_top hab T' (fun _ _ => trivial)
    (hT'.trans (Subgroup.le_topologicalClosure _))
  obtain ⟨⟨Φ, -⟩, -⟩ := selTwist O (G k Ω) (QO l O) _ (rho l e ψ) ψ (tw_apply l e ψ) (galOf k L Ω)
    (fun u hu => hψ hu) _ (conjStable_shaFam k Ω l)
  have hχ : chiO k Ω l O ^ (-(e : ℤ)) =
      (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l ^ (-(e : ℤ))) :=
    MonoidHom.ext fun g => (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) _).symm
  have hb := (qoBase l (G k Ω) O (cycZ k Ω l ^ (-(e : ℤ))) (galOf k L Ω) (shaFam k Ω l)).1
  rw [← hχ, Φ.length_eq] at hb
  have hs : shaLen D (e : ℤ) = _ := (shaLenEq k L Ω l D e).1
  refine (selUp O (G k Ω) (QO l O) (rho l e ψ) (galOf k L Ω) ⊤ le_top _ (conjStable_shaFam k Ω l)).1.trans
    (add_le_add (le_of_eq ?_) (hk.trans ?_))
  · rw [hs]
    exact hb
  · unfold h0
    gcongr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SignLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem aux {O W M : Type} [CommRing O] [IsDomain O] [Group W] [AddCommGroup M] [Module O M] {N : ℕ} [NeZero N]
    (H : Subgroup (ZMod N)ˣ) [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))]
    (π : Representation O W M) (cl : W →* (ZMod N)ˣ) (hcl : Function.Surjective cl)
    (hker : ∀ g, cl g ∈ H → ∀ x, π g x = x) (h2 : IsUnit (2 : O)) (s : ℕ) (c : W) (hcc : cl c = -1)
    (T : Finset (DirichletCharacter O N)) (hT : evenSet O H s ⊆ ↑T) :
    Module.length O (Module.End.eigenspace (π c) ((-1 : O) ^ s)) ≤
      ∑ χ ∈ T, Module.length O (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        ((χ.toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype)) := by
  classical
  let _ : Fintype (((ZMod N)ˣ ⧸ H) →* Oˣ) := Fintype.ofFinite _
  let p : W →* (ZMod N)ˣ ⧸ H := (QuotientGroup.mk' H).comp cl
  have hp : Function.Surjective p := (QuotientGroup.mk'_surjective H).comp hcl
  have hpc : p c = QuotientGroup.mk' H (-1) := by
    show QuotientGroup.mk' H (cl c) = _
    rw [hcc]
  let f : (((ZMod N)ˣ ⧸ H) →* Oˣ) → DirichletCharacter O N := fun ψ =>
    MulChar.ofUnitHom (ψ.comp (QuotientGroup.mk' H))
  have hf : ∀ ψ, (f ψ).toUnitHom = ψ.comp (QuotientGroup.mk' H) := fun ψ =>
    MulChar.equivToUnitHom.apply_symm_apply _
  have finj : Function.Injective f := fun ψ ψ' h => by
    have h' : ψ.comp (QuotientGroup.mk' H) = ψ'.comp (QuotientGroup.mk' H) := by rw [← hf, ← hf, h]
    exact (MonoidHom.cancel_right (QuotientGroup.mk'_surjective H)).1 h'
  have key := lenEigSign O W ((ZMod N)ˣ ⧸ H) M π p hp
    (fun g hg x => hker g ((QuotientGroup.eq_one_iff _).1 hg) x) h2 c ((-1) ^ s)
    (by rw [hpc, ← map_mul]; simp) (by rw [← mul_pow]; simp)
    (Finset.univ.filter fun ψ => ψ (p c) = (-1) ^ s) (fun ψ h => by simpa using h)
  have hs : (((-1 : Oˣ) ^ s : Oˣ) : O) = (-1) ^ s := by simp
  rw [hs] at key
  refine key.trans ?_
  have hE : ∀ ψ : ((ZMod N)ˣ ⧸ H) →* Oˣ, eig π (ψ.comp p) =
      eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        (((f ψ).toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype) := by
    intro ψ
    ext x
    rw [mem_eig, mem_eig, hf]
    exact ⟨fun h g => h g.1, fun h g => h ⟨g, trivial⟩⟩
  rw [Finset.sum_congr rfl fun ψ _ => congrArg (fun S : Submodule O M => Module.length O S) (hE ψ),
    ← Finset.sum_image (f := fun χ : DirichletCharacter O N => Module.length O
      (eig (π.comp (⊤ : Subgroup W).subtype : Representation O (⊤ : Subgroup W) M)
        ((χ.toUnitHom.comp cl).comp (⊤ : Subgroup W).subtype))) finj.injOn]
  refine Finset.sum_le_sum_of_subset fun χ hχ => ?_
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hχ
  have hψ' := (Finset.mem_filter.1 hψ).2
  refine hT ⟨fun u hu => ?_, ?_⟩
  · rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu, map_one]
  · have : f ψ (((-1 : (ZMod N)ˣ)) : ZMod N) = (((f ψ).toUnitHom (-1) : Oˣ) : O) := (MulChar.coe_toUnitHom _ _).symm
    rw [hf, MonoidHom.comp_apply, ← hpc, hψ', hs] at this
    simpa using this

theorem UpperTheory.V.Chr.signLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [HasEnoughRootsOfUnity O (Monoid.exponent ((ZMod N)ˣ ⧸ H))], l ≠ 2 → ∀ (e s : ℕ) (c : G ℚ Ω), IsConjOm c.toRingEquiv →
          ∀ T : Finset (DirichletCharacter O N), evenSet O H s ⊆ ↑T →
          Module.length O (Module.End.eigenspace (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) c) ((-1 : O) ^ s)) ≤
            ∑ χ ∈ T, eigL l e (levH ℚ Ω H) (dirG ℚ Ω χ) := by
  intro Ω _ _ _ N _ H l hl O _ _ _ _ _ _ hl2 e s c hc T hT
  have h2 : IsUnit (2 : O) := by
    have := (dvrFacts l O).2.2.2.2.2.2.2.2 2 fun h =>
      hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h)
    simpa using this
  have hker : ∀ g, cls ℚ Ω N g ∈ H → ∀ x, shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H) g x = x :=
    fun g hg x => selRep_of_mem _ (levH ℚ Ω H) _ (g := g) (Subgroup.mem_comap.2 hg) x
  exact aux H (shaRep (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) l (levH ℚ Ω H)) (cls ℚ Ω N) (clsOnto Ω N).1
    hker h2 s c ((clsFacts ℚ Ω N).2.2.2.1 c hc) T hT
end

