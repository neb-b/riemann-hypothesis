module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdHalf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CkCastMod
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

private abbrev ckPull {A Γ Γ' : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    (p : Γ →* Γ') (hp : Continuous p) (M : FRep A Γ') : FRep A Γ where
  X := M.X
  ρ := M.ρ.comp p
  cont := M.cont.comp (hp.prodMap continuous_id)

private theorem ck_card {X Y C : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup C] [Finite Y]
    (t : X →+ Y) (q : X →+ C) (hq : Function.Surjective q) (h : ∀ x, t x = 0 → q x = 0) :
    Nat.card C ≤ Nat.card Y := by
  choose s hs using hq
  refine Nat.card_le_card_of_injective (fun c => t (s c)) fun c c' e => ?_
  have := h (s c - s c') (by rw [map_sub]; exact sub_eq_zero.2 e)
  rwa [map_sub, hs, hs, sub_eq_zero] at this

private theorem ck_onto (l : ℕ) {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)
    (hM : ∀ m : D.M.X, l • m = 0) {I : Type} (E : I → Type) [∀ i, Group (E i)] [∀ i, TopologicalSpace (E i)]
    (φ : ∀ i, E i →* Γ) (hφ : ∀ i, Continuous (φ i)) (j : P.ι → I) (hj : Function.Injective j)
    (α : ∀ w, P.G w ≃ₜ* E (j w)) (hα : ∀ w g, φ (j w) (α w g) = P.φ w g) (ho : ∀ w, SecondCohomologyRightExactModL l (P.G w)) :
    ∃ q : (∀ i, H2 (ckPull (φ i) (hφ i) D.M).ρ) →ₗ[A] ∀ w, H2 (D.Q w).ρ, Function.Surjective q ∧
      ∀ z : H2 D.M.ρ, q (fun i => resH2 D.M.ρ (φ i) (hφ i) z) = D.loc2 z := by
  classical
  let q1 : ∀ w, H2 (ckPull (φ (j w)) (hφ _) D.M).ρ →ₗ[A] H2 (D.Q w).ρ := fun w =>
    compatiblePairH2 (ckPull (φ (j w)) (hφ _) D.M).ρ (D.Q w).ρ (α w).toMulEquiv.toMonoidHom (α w).continuous (D.π w)
      continuous_of_discreteTopology fun g m => by
        rw [← D.equiv, ← hα]; rfl
  have hq1 : ∀ w, Function.Surjective (q1 w) := by
    intro w y
    obtain ⟨x, rfl⟩ := ho w A (ckPull (P.φ w) (P.cont w) D.M) (D.Q w) hM (D.π w) (D.equiv w) (D.surj w) y
    refine ⟨compatiblePairH2 (ckPull (P.φ w) (P.cont w) D.M).ρ (ckPull (φ (j w)) (hφ _) D.M).ρ
      (α w).symm.toMulEquiv.toMonoidHom (α w).symm.continuous LinearMap.id continuous_id (fun g m => ?_) x, ?_⟩
    · show D.M.ρ (P.φ w ((α w).symm g)) m = D.M.ρ (φ (j w) g) m
      rw [← hα, (α w).apply_symm_apply]
    · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      show D.π w (f.1 ((α w).symm (α w g.1), (α w).symm (α w g.2))) = D.π w (f.1 g)
      rw [(α w).symm_apply_apply, (α w).symm_apply_apply]
  refine ⟨LinearMap.pi fun w => (q1 w).comp (LinearMap.proj (j w)), fun y => ?_, fun z => ?_⟩
  · choose x hx using fun w => hq1 w (y w)
    refine ⟨∑ w, Pi.single (j w) (x w), funext fun w => ?_⟩
    rw [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Finset.sum_apply,
      Finset.sum_eq_single w (fun w' _ h => Pi.single_eq_of_ne (fun e => h (hj e).symm) _) (by simp),
      Pi.single_eq_same, hx]
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    funext w
    refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
    show D.π w (f.1 (φ (j w) (α w g.1), φ (j w) (α w g.2))) = D.π w (f.1 (P.φ w g.1, P.φ w g.2))
    rw [hα, hα]

private theorem ck_castMod (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) :
    ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l) (PadicInt.toZModPow 1 x) = PadicInt.toZMod x := by
  have h : (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).comp (PadicInt.toZModPow 1) = PadicInt.toZMod := by
    ext y
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 y)
    rw [sub_add_cancel y (PadicInt.appr y 1 : ℤ_[l]) |>.symm, ← hc]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    rw [ZMod.natCast_self]; simp
  exact RingHom.congr_fun h x


open GlobalTheory.Published GlobalTheory.Published.PoitouTate in
private theorem ck_pt (hP : GlobalTheory.Published.PoitouTateNormalised) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (h2 : l ≠ 2) (S : Set (HeightOneSpectrum (𝓞 F))) (hf : S.Finite)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (B : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω) (hB : ∀ v, IsPlaceOver (B v) v)
    (ε : GS Ω S →* ℤ_[l]ˣ) (hε : ε.comp (toGS Ω S) = cycZ F Ω l)
    (A : Type) [CommRing A] (M : FRep A (GS Ω S)) (hM : ∀ m : M.X, l • m = 0) (C : Type) [AddCommGroup C]
    (q : (∀ v : S, H2 (ckPull (locHom S (B v)) (continuous_locHom S (B v)) M).ρ) →+ C) (hq : Function.Surjective q)
    (h0 : ∀ z : H2 M.ρ, q (fun v => resH2 M.ρ (locHom S (B v)) (continuous_locHom S (B v)) z) = 0) :
    Nat.card C ≤ Nat.card {f : M.X →+ ZMod l // ∀ g m, f (M.ρ g m) = PadicInt.toZMod ((ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  obtain ⟨S, rfl⟩ := hf.exists_finset_coe
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  obtain ⟨inst⟩ : Nonempty (Module (ZMod (l ^ 1)) M.X) := ⟨AddCommGroup.zmodModule (by simpa using hM)⟩
  obtain ⟨hρ, -, -, e, he⟩ := scal A _ M (l ^ 1)
  have hv := fun v : S => (@scal A _ _ _ _ (ckPull (locHom (S : Set (HeightOneSpectrum (𝓞 F))) (B v)) (continuous_locHom _ (B v)) M) (l ^ 1) inst).2.2.2
  choose ev hev using hv
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero ((l ^ 1 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hl.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  let μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ :=
    (Units.map (PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1)).toMonoidHom).comp ε
  have hμ : μ.comp (toGS Ω _) = cycMod F Ω l 1 := by
    rw [cycMod, ← hε]; rfl
  let ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M.X := zmodRep (l ^ 1) M.ρ
  obtain ⟨inv, -, hN⟩ := hP F Ω l 1 (Or.inl h2) one_pos ζ hζ
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hex, -⟩, -⟩ :=
    hN S (fun v hv => hS v hv) (fun v => B v) (fun v => hB v) μ hμ M.X ρ' hρ
  haveI : Finite (TDual (ZMod (l ^ 1)) M.X) :=
    (Finite.of_injective _ (DFunLike.coe_injective (F := M.X →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1))) :
      Finite (M.X →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  haveI : Finite (H0 (twDual μ ρ')) := Subtype.finite
  haveI : Finite (Module.Dual (ZMod (l ^ 1)) (H0 (twDual μ ρ'))) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := H0 (twDual μ ρ') →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
  refine (ck_card ((tr2 S (fun v => B v) μ (invAt S (fun v => B v) μ hμ inv) ρ').toAddMonoidHom.comp
    (AddEquiv.piCongrRight ev).toAddMonoidHom) q hq fun x hx => ?_).trans ?_
  · obtain ⟨z, hz⟩ := (hex _).1 hx
    obtain ⟨z, rfl⟩ := e.surjective z
    rw [← h0 z]
    congr 1
    funext v
    apply (ev v).injective
    refine (congrFun hz v).symm.trans ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [he f ⟨f.1, f.2⟩ rfl]
    exact (hev v (restrictCocycles2 M.ρ _ (continuous_locHom _ (B v)) f) _ rfl).symm
  · rw [Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)), Subspace.dual_finrank_eq,
      ← Module.natCard_eq_pow_finrank]
    let c := ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)
    haveI : Finite (M.X →+ ZMod l) := Finite.of_injective _ (DFunLike.coe_injective (F := M.X →+ ZMod l))
    refine Nat.card_le_card_of_injective (fun y => ⟨c.toAddMonoidHom.comp
      (show M.X →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1) from y.1).toAddMonoidHom, fun g m => ?_⟩) fun y y' h => ?_
    · have e := congrArg (fun φ : TDual (ZMod (l ^ 1)) M.X => φ (M.ρ g m)) (y.2 g)
      simp only [twDual_apply] at e
      have e2 : zmodRep (l ^ 1) M.ρ g⁻¹ (M.ρ g m) = m := by
        show M.ρ g⁻¹ (M.ρ g m) = m
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [e2] at e
      show c (y.1 (M.ρ g m)) = _ * c (y.1 m)
      rw [← e, map_mul, ← ck_castMod]
      rfl
    · apply Subtype.ext
      apply LinearMap.ext
      intro m
      apply c.injective
      exact DFunLike.congr_fun (congrArg Subtype.val h) m

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arCk :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (A : Type) [CommRing A] (D : Dat A (plOf (globOf r V))), (∀ m : D.M.X, l • m = 0) → Nat.card D.Ck2 ≤ Nat.card {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod (((globOf r V).ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r A _ D hM
  let j : (plOf (globOf r V)).ι → V.S' := fun w => match w with
    | .inl v => ⟨Subtype.val v, V.sub (Or.inl v.2)⟩
    | .inr u => ⟨Subtype.val u, V.sub (Or.inr (Or.inl u.2))⟩
  have hj : Function.Injective j := by
    rintro (v | u) (v' | u') h <;> have h' := congrArg Subtype.val h
    · exact congrArg Sum.inl (Subtype.ext h')
    · exact absurd (h' ▸ v.2 : ((l : ℕ) : 𝓞 (Lp L)) ∈ (Subtype.val u').asIdeal) (s.St_l _ u'.2)
    · exact absurd (h'.symm ▸ v'.2 : ((l : ℕ) : 𝓞 (Lp L)) ∈ (Subtype.val u).asIdeal) (s.St_l _ u.2)
    · exact congrArg Sum.inr (Subtype.ext h')
  choose β hβ using fun v : V.S' => decSplit L Ω (s.A v) (V.split v v.2)
  let α : ∀ w, (plOf (globOf r V)).G w ≃ₜ* Dec (F := Lp L) (s.A (j w)) := fun w => match w with
    | .inl v => β (j (.inl v))
    | .inr u => β (j (.inr u))
  obtain ⟨q, hq, hz⟩ := ck_onto l D hM (fun v : V.S' => Dec (F := Lp L) (s.A v)) (fun v => locHom V.S' (s.A v))
    (fun v => continuous_locHom V.S' (s.A v)) j hj α
    (by
      rintro (v | u) g
      · exact congrArg (toGS Ω V.S') (hβ (j (.inl v)) g)
      · exact congrArg (toGS Ω V.S') (hβ (j (.inr u)) g))
    (by
      rintro (v | u)
      · exact (arLoc hP L Ω l _ _ (s.hw (Subtype.val v))).2.1
      · exact (arLoc hP L Ω l _ _ (s.hw (Subtype.val u))).2.1)
  refine ck_pt hP.pt (Lp L) Ω l s.odd V.S' V.fin (fun v hv => V.sub (Or.inl hv)) s.A s.hA V.ε V.hε A D.M hM D.Ck2
    ((LinearMap.range D.loc2).mkQ.comp q).toAddMonoidHom ((Submodule.mkQ_surjective _).comp hq) fun z => ?_
  exact (congrArg (LinearMap.range D.loc2).mkQ (hz z)).trans ((Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdCount
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odCount :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X] (D : Dat x.A (plOf G)) (d : ℕ) (dv : L.Vl → ℕ), l ≠ 2 → IsOd h x X D → CohAx G d dv → Finite D.H2LocalConditions ∧ Finite D.Ck2 ∧ Nat.card D.H2LocalConditions ≤ Nat.card D.Sel * (∏ v, Nat.card (H0 (D.Q (inV G v)).ρ)) * Nat.card {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  intro l _ L G G0 h n x X _ _ _ D d dv hl hD hC
  obtain ⟨hM, hfixc, hQv⟩ := odHalf l L G G0 h n x X D hl hD
  obtain ⟨ktM, ktQ, ktJ⟩ := odKill l L G G0 h n x X D hD
  set N := Nat.card X ^ (x.a * (n - x.a)) with hN
  have hNpos : 0 < N := pow_pos Nat.card_pos _
  have fM := hC.fin x.A D.M ktM
  have fQ : ∀ w, Finite (H1 (D.Q w).ρ) ∧ Finite (H2 (D.Q w).ρ) := by
    intro w
    cases w with
    | inl v => exact hC.finV v x.A (D.Q (inV G v)) (ktQ _)
    | inr u => exact hC.finU u x.A (D.Q (inU G u)) (ktQ _)
  let dw : (plOf G).ι → ℕ := Sum.elim dv (fun _ => 0)
  let e : (plOf G).ι → ℕ := Sum.elim (fun v => Nat.card (H0 (D.Q (inV G v)).ρ)) (fun _ => 1)
  have hglob : Nat.card (H2 D.M.ρ) * N ^ ∑ w, dw w ≤ Nat.card (H1 D.M.ρ) := by
    obtain ⟨c, hc, hE⟩ := hC.ge
    have E := hE x.A D.M ktM
    have hfix : ∀ i, Nat.card {m // D.M.ρ (c i) m = m} = N := fun i => hfixc (c i) (hc i).1 (hc i).2
    simp only [hfix, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hM] at E
    have hsum : ∑ w, dw w = d := by
      show ∑ w : L.Vl ⊕ L.St, dw w = d
      rw [Fintype.sum_sum_type]
      simp [dw, hC.sum]
    rw [hsum]
    have h0pos : 0 < Nat.card (H0 D.M.ρ) := Nat.card_pos
    have key : Nat.card (H0 D.M.ρ) * Nat.card (H2 D.M.ρ) * N ^ d = Nat.card (H1 D.M.ρ) := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hNpos d)
      rw [← E]
      ring
    calc Nat.card (H2 D.M.ρ) * N ^ d ≤ Nat.card (H0 D.M.ρ) * (Nat.card (H2 D.M.ρ) * N ^ d) :=
          Nat.le_mul_of_pos_left _ h0pos
      _ = Nat.card (H1 D.M.ρ) := by rw [← key, mul_assoc]
  have hloc : ∀ w, Nat.card (H1 (D.Q w).ρ) ≤
      Nat.card (H1ur (D.Q w).ρ ((plOf G).J w)) * Nat.card (H2 (D.Q w).ρ) * e w * N ^ dw w := by
    intro w
    cases w with
    | inl v =>
      have E := hC.leV v x.A (D.Q (inV G v)) (ktQ _)
      rw [hQv v] at E
      haveI := (fQ (inV G v)).1
      have hur : 0 < Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) := Nat.card_pos
      have key : Nat.card (H0 (D.Q (inV G v)).ρ) * Nat.card (H2 (D.Q (inV G v)).ρ) * N ^ dv v
          ≤ Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) *
            Nat.card (H2 (D.Q (inV G v)).ρ) * Nat.card (H0 (D.Q (inV G v)).ρ) * N ^ dv v := by
        calc _ ≤ Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) *
              (Nat.card (H0 (D.Q (inV G v)).ρ) * Nat.card (H2 (D.Q (inV G v)).ρ) * N ^ dv v) :=
              Nat.le_mul_of_pos_left _ hur
          _ = _ := by ring
      exact E.le.trans key
    | inr u =>
      have E := hC.leU u x.A (D.Q (inU G u)) (ktQ _)
      have ur := ((hC.ur u) x.A (D.Q (inU G u)) (ktQ _) (ktJ u)).1
      rw [pow_zero, mul_one] at E
      have key : Nat.card (H0 (D.Q (inU G u)).ρ) * Nat.card (H2 (D.Q (inU G u)).ρ)
          ≤ Nat.card (H1ur (D.Q (inU G u)).ρ (L.Ju u)) * Nat.card (H2 (D.Q (inU G u)).ρ) * 1 * N ^ 0 := by
        rw [pow_zero, mul_one, mul_one]
        exact Nat.mul_le_mul_right _ ur
      exact E.le.trans key
  obtain ⟨hfin, hle⟩ := count x.A G.Γ (plOf G) D N dw e hNpos fM.1 fM.2 fQ hglob hloc
  have hfin2 : Finite D.Ck2 := by
    haveI : Fintype (plOf G).ι := (plOf G).fin
    haveI : ∀ w, Finite (H2 (D.Q w).ρ) := fun w => (fQ w).2
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨hfin, hfin2, ?_⟩
  have hck := hC.ck x.A D ktM
  have hprod : ∏ w, e w = ∏ v, Nat.card (H0 (D.Q (inV G v)).ρ) := by
    show ∏ w : L.Vl ⊕ L.St, e w = _
    rw [Fintype.prod_sum_type]
    simp [e]
  calc Nat.card D.H2LocalConditions ≤ (Nat.card D.Sel * ∏ w, e w) * Nat.card D.Ck2 := hle
    _ ≤ _ := by rw [hprod]; exact Nat.mul_le_mul_left _ hck
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdLam
section
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D D'' : Dat x.A (plOf G)) (_ : IsOd h x X D) (_ : IsOd h x X'' D'') (g : D.Hom D''), Function.Surjective g.f → (∀ u, UrAx l (L.Ju u)) → ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
  intro l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy
  have hs : ∀ w, Function.Surjective (g.fq w) := by
    intro w q
    obtain ⟨m, rfl⟩ := D''.surj w q
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨D.π w m, g.comm w m⟩
  have top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
    rintro w hw y'' ⟨-, Y, hY⟩
    obtain ⟨Y, rfl⟩ := hs _ Y
    refine ⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩
    rw [hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]
  rcases w with v | u
  · exact top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy
  · obtain ⟨hz, Y, hY⟩ := hy
    obtain ⟨-, k1, k2⟩ := odKill l L G G0 h n x X D o
    obtain ⟨-, -, k3⟩ := odKill l L G G0 h n x X'' D'' o''
    obtain ⟨y, a1, a2, a3⟩ := (hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u))
      (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))
    exact ⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.TranslDD
section
open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.B2

section

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

def mk2 (P : Fin g → Matrix (Fin n) (Fin n) X) (Z : Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun a b => ⟨0, 0, fun j => P j a b, Z a b⟩

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (AddMonoidHom.mk' DD.a DD.add_a) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j :=
  map_sum (AddMonoidHom.mk' (fun d : DD X g => d.ep j) fun x y => DD.add_ep x y j) f s

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j :=
  map_sum (AddMonoidHom.mk' (fun d : DD X g => d.ep' j) fun x y => DD.add_ep' x y j) f s

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta :=
  map_sum (AddMonoidHom.mk' DD.eta DD.add_eta) f s

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

theorem epsPrimeEtaMatrix_add (P P' : Fin g → Matrix (Fin n) (Fin n) X) (Z Z') :
    mk2 P Z + mk2 P' Z' = mk2 (fun j => P j + P' j) (Z + Z') := by
  ext a b <;> simp [mk2]

theorem epsPrimeEtaMatrix_sub (P P' : Fin g → Matrix (Fin n) (Fin n) X) (Z Z') :
    mk2 P Z - mk2 P' Z' = mk2 (fun j => P j - P' j) (Z - Z') := by
  ext a b <;> simp [mk2, sub_eq_add_neg]

theorem epsPrimeEtaMatrix_smul (c : A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    c • mk2 P Z = mk2 (fun j => c • P j) (c • Z) := by
  ext a b <;> simp [mk2, Algebra.smul_def, alg_eq]

theorem neg_transpose_epsPrimeEtaMatrix (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    -(mk2 P Z)ᵀ = mk2 (fun j => -(P j)ᵀ) (-Zᵀ) := by
  ext a b <;> simp [mk2]

theorem epsPrimeEtaMatrix_apply_eq_zero_iff {P : Fin g → Matrix (Fin n) (Fin n) X} {Z} {a b} :
    mk2 P Z a b = 0 ↔ (∀ j, P j a b = 0) ∧ Z a b = 0 :=
  ⟨fun h => ⟨fun j => congrArg (fun d : DD X g => d.ep' j) h, congrArg DD.eta h⟩,
    fun h => DD.ext rfl rfl (funext h.1) h.2⟩

theorem epsPrimeEtaMatrix_injective_pair {P P' : Fin g → Matrix (Fin n) (Fin n) X} {Z Z'} (h : mk2 P Z = mk2 P' Z') : P = P' ∧ Z = Z' :=
  ⟨funext fun j => Matrix.ext fun a b => congrArg (fun M : Matrix (Fin n) (Fin n) (DD X g) => (M a b).ep' j) h,
    Matrix.ext fun a b => congrArg (fun M : Matrix (Fin n) (Fin n) (DD X g) => (M a b).eta) h⟩

theorem evenOddBlockMatrix_mem_adjointDeformSubspace {a : ℕ} {P : Fin g → Matrix (Fin n) (Fin n) X} {Z} (hP : ∀ j, P j ∈ Ev A X n a)
    (hZ : Z ∈ Od A X n a) : mk2 P Z ∈ W2 n A X g a := fun i j =>
  ⟨fun e => ⟨fun _ => rfl, fun _ => rfl, fun h => by simp at h, fun _ => (hZ i j).1 e⟩,
    fun e => ⟨fun _ => rfl, fun _ => rfl, fun _ => funext fun m => (hP m i j).2 e, fun h => by simp at h⟩⟩

theorem exists_evenOddBlock_decomposition_of_mem {a : ℕ} {M : Matrix (Fin n) (Fin n) (DD X g)} (h : M ∈ W2 n A X g a) :
    ∃ P Z, (∀ j, P j ∈ Ev A X n a) ∧ Z ∈ Od A X n a ∧ M = mk2 P Z := by
  refine ⟨fun j => M.map fun d => d.ep' j, M.map DD.eta, fun m i j => ⟨fun _ => trivial, fun e => ?_⟩,
    fun i j => ⟨fun e => ((h i j).1 e).2.2.2 rfl, fun _ => trivial⟩, Matrix.ext fun i j => ?_⟩
  · exact congrFun (((h i j).2 e).2.2.1 rfl) m
  · by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact DD.ext (((h i j).1 e).1 rfl) (((h i j).1 e).2.1 rfl) rfl rfl
    · exact DD.ext (((h i j).2 e).1 rfl) (((h i j).2 e).2.1 rfl) rfl rfl

theorem algebraMap_matrix_mul_epsPrimeEtaMatrix (M : Matrix (Fin n) (Fin n) A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    M.map (algebraMap A (DD X g)) * mk2 P Z =
      mk2 (fun j => M.map (algebraMap A X) * P j) (M.map (algebraMap A X) * Z) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

theorem epsPrimeEtaMatrix_mul_algebraMap_matrix (M : Matrix (Fin n) (Fin n) A) (P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    mk2 P Z * M.map (algebraMap A (DD X g)) =
      mk2 (fun j => P j * M.map (algebraMap A X)) (Z * M.map (algebraMap A X)) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

theorem epM_mul_epsPrimeEtaMatrix (Y P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    DD.epM Y * mk2 P Z = mk2 (fun _ => 0) (∑ j, Y j * P j) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, Matrix.sum_apply]
  exact Finset.sum_comm

theorem epsPrimeEtaMatrix_mul_epM (Y P : Fin g → Matrix (Fin n) (Fin n) X) (Z) :
    mk2 P Z * DD.epM Y = mk2 (fun _ => 0) (∑ j, P j * Y j) := by
  ext a b <;> simp [Matrix.mul_apply, mk2, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, Matrix.sum_apply]
  exact Finset.sum_comm

private theorem ev_od {a : ℕ} {P Y : Matrix (Fin n) (Fin n) X} (hP : P ∈ Ev A X n a) (hY : Y ∈ Od A X n a) :
    Y * P - P * Y ∈ Od A X n a := by
  refine sub_mem (fun i j => ⟨fun e => ?_, fun _ => trivial⟩) (fun i j => ⟨fun e => ?_, fun _ => trivial⟩)
  · refine (Submodule.mem_bot A).2 ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
    · rw [(Submodule.mem_bot A).1 ((hY i c).1 h), zero_mul]
    · rw [(Submodule.mem_bot A).1 ((hP c j).2 (by tauto)), mul_zero]
  · refine (Submodule.mem_bot A).2 ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
    · rw [(Submodule.mem_bot A).1 ((hY c j).1 (by tauto)), mul_zero]
    · rw [(Submodule.mem_bot A).1 ((hP i c).2 h), zero_mul]

end

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]

theorem rho1_conj_block_matrix (g g' : F.G₀) (P : Fin k.g → Matrix (Fin n) (Fin n) X) (Z) :
    ∃ Z', k.ρ1 X g * mk2 P Z * k.ρ1 X g' = mk2 (fun j => x.ρX X g * P j * x.ρX X g') Z' := by
  simp only [Kap.ρ1, NP.ρX]
  rw [mul_assoc (1 + _), algebraMap_matrix_mul_epsPrimeEtaMatrix, add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, ← mul_assoc, mul_add, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_add, epsPrimeEtaMatrix_mul_algebraMap_matrix]
  simp only [add_zero]
  exact ⟨_, rfl⟩

theorem rho1_conj_block_zero (g g' : F.G₀) (Z) :
    k.ρ1 X g * mk2 (fun _ => 0) Z * k.ρ1 X g' = mk2 (fun _ => 0) (x.ρX X g * Z * x.ρX X g') := by
  simp only [Kap.ρ1, NP.ρX]
  rw [mul_assoc (1 + _), algebraMap_matrix_mul_epsPrimeEtaMatrix, add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, ← mul_assoc, mul_add, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_add, epsPrimeEtaMatrix_mul_algebraMap_matrix]
  simp

noncomputable def cmm (v : F.Vl) (P : Fin k.g → Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) X :=
  ∑ j, ((k.Y j v).map (algebraMap x.A X) * P j - P j * (k.Y j v).map (algebraMap x.A X))

theorem weyl_conj_block_matrix (v : F.Vl) (P : Fin k.g → Matrix (Fin n) (Fin n) X) (Z) :
    k.wi1 X v * mk2 P Z * k.w1 X v =
      mk2 (fun j => x.wiX X v * P j * x.wX X v) (x.wiX X v * (Z + cmm k X v P) * x.wX X v) := by
  simp only [Kap.w1, Kap.wi1, NP.wX, NP.wiX, cmm]
  rw [mul_assoc _ (1 + _), add_mul, one_mul, epM_mul_epsPrimeEtaMatrix, epsPrimeEtaMatrix_add, mul_assoc, ← mul_assoc (mk2 _ _), mul_sub, mul_one,
    epsPrimeEtaMatrix_mul_epM, epsPrimeEtaMatrix_sub, epsPrimeEtaMatrix_mul_algebraMap_matrix, algebraMap_matrix_mul_epsPrimeEtaMatrix]
  simp only [add_zero, sub_zero, Finset.sum_sub_distrib, mul_assoc, add_sub_assoc]

theorem cmm_mem (v : F.Vl) {P : Fin k.g → Matrix (Fin n) (Fin n) X} (hP : ∀ j, P j ∈ Ev x.A X n x.a) :
    cmm k X v P ∈ Od x.A X n x.a :=
  Submodule.sum_mem _ fun j _ => ev_od (hP j) fun a b => ⟨fun e => by
    have : k.Y j v a b = 0 := (k.Y_mem j v a b).1 e
    simp [this], fun _ => trivial⟩

theorem od_diag (v : F.Vl) {Z : Matrix (Fin n) (Fin n) X} (hZ : Z ∈ Od x.A X n x.a) (i : Fin n) :
    (x.wiX X v * Z * x.wX X v) i i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : decide ((b : ℕ) < x.a) = x.ty v i
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro a _
    by_cases ha : x.ty v i = decide ((a : ℕ) < x.a)
    · rw [(Submodule.mem_bot x.A).1 ((hZ a b).1 (by simpa using (hb.trans ha).symm)), mul_zero]
    · have := (tyCard l F n x v 0).2.2.2 i a ha
      simp only [NP.wiX, Matrix.map_apply, this, map_zero, zero_mul]
  · simp only [NP.wX, Matrix.map_apply, x.w_blk v b i hb, map_zero, mul_zero]

theorem isLocallyConstant_rho1_of_algebraMap_pow_eq_zero (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) : IsLocallyConstant (k.ρ1 X) := by
  have aux : ∀ f : F.G₀ → Matrix (Fin n) (Fin n) x.A,
      (∀ i j, AdicCont (Ideal.span {x.t}) fun g => f g i j) → ∀ (R : Type) [CommRing R] [Algebra x.A R],
      algebraMap x.A R (x.t ^ m) = 0 → ∀ g0, ∀ᶠ g in nhds g0, (f g).map (algebraMap x.A R) = (f g0).map (algebraMap x.A R) := by
    intro f hf R _ _ hR g0
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hf i j m).eventually_eq g0]
      with g hg
    refine Matrix.ext fun i j => ?_
    have h2 := Ideal.Quotient.eq.1 (hg i j)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
    obtain ⟨c, hc⟩ := h2
    have h3 := congrArg (algebraMap x.A R) hc
    rw [RingHom.map_sub, map_mul, hR, zero_mul, sub_eq_zero] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  filter_upwards [Filter.eventually_all.2 fun j => aux (k.κ j) (k.mem j).2.1 X hm g0,
    aux (mat x.ρ) (by rw [← PowerSeries.maximalIdeal_eq_span_X]; exact x.cont) (DD X k.g)
      (by rw [alg_eq, hm, map_zero]) g0] with g h1 h2
  simp only [Kap.ρ1, NP.ρX, h1, h2]

end UpperTheory.V.Pa.B2
end

