module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIso
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Semi

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']
  (e : V ≃+ V') (he : ∀ (c : F) (x : V), e (c • x) = r c • e x)

include he in
private theorem symm_smul (c : F') (y : V') : e.symm (c • y) = r.symm c • e.symm y := by
  apply e.injective
  rw [he]
  simp

private def smap (W : Submodule F V) : Submodule F' V' where
  carrier := e '' W
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, W.add_mem ha hb, map_add e a b⟩
  zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨r.symm c • a, W.smul_mem _ ha, by rw [he]; simp⟩

private def scomap (W : Submodule F' V') : Submodule F V where
  carrier := e ⁻¹' W
  add_mem' := by
    intro a b ha hb
    simpa using W.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_preimage, SetLike.mem_coe, he] at ha ⊢
    exact W.smul_mem _ ha

private theorem mem_smap {W : Submodule F V} {y : V'} : y ∈ smap r e he W ↔ e.symm y ∈ W := by
  change y ∈ e '' (W : Set V) ↔ _
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨e.symm y, h, by simp⟩

private def smapE : Submodule F V ≃ Submodule F' V' where
  toFun := smap r e he
  invFun := scomap r e he
  left_inv W := by
    ext x
    change e x ∈ smap r e he W ↔ _
    rw [mem_smap]
    simp
  right_inv W := by
    ext y
    rw [mem_smap]
    change e (e.symm y) ∈ W ↔ _
    simp

private def eRes (W : Submodule F V) : W ≃+ smap r e he W where
  toFun x := ⟨e x, (mem_smap r e he).2 (by simp)⟩
  invFun y := ⟨e.symm y, (mem_smap r e he).1 y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

include he in
private theorem charpoly_semi [FiniteDimensional F V] [FiniteDimensional F' V']
    (g : Module.End F V) (g' : Module.End F' V') (hg : ∀ x, e (g x) = g' (e x)) :
    LinearMap.charpoly g' = (LinearMap.charpoly g).map r.toRingHom := by
  classical
  let b := Module.finBasis F V
  have hf : ∀ f : Fin (Module.finrank F V) →₀ F,
      Finsupp.mapRange r.symm (map_zero r.symm) (Finsupp.mapRange r (map_zero r) f) = f := by
    intro f
    ext i
    simp
  let repr' : V' ≃ₗ[F'] (Fin (Module.finrank F V) →₀ F') :=
    { toFun := fun y => Finsupp.mapRange r (map_zero r) (b.repr (e.symm y))
      invFun := fun c => e (b.repr.symm (Finsupp.mapRange r.symm (map_zero r.symm) c))
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro c y
        ext i
        simp [symm_smul r e he]
      left_inv := by
        intro y
        show e (b.repr.symm (Finsupp.mapRange r.symm _ (Finsupp.mapRange r _ (b.repr (e.symm y))))) = y
        rw [hf]
        simp
      right_inv := by
        intro c
        ext i
        simp }
  let b' : Module.Basis (Fin (Module.finrank F V)) F' V' := Module.Basis.ofRepr repr'
  have hb' : ∀ j, b' j = e (b j) := by
    intro j
    simp [b', repr']
  rw [← LinearMap.charpoly_toMatrix g b, ← LinearMap.charpoly_toMatrix g' b', ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  show (Finsupp.mapRange r (map_zero r) (b.repr (e.symm (e (g (b j)))))) i = _
  simp

end Semi

private theorem semilinear_equiv_conjugate_endomorphism {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (s : F[X] → ℂ) (s' : F'[X] → ℂ)
    (hs : ∀ P, s' (P.map r.toRingHom) = s P) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F' V']
      [FiniteDimensional F' V'] (e : V ≃+ V') (_ : ∀ (c : F) (x : V), e (c • x) = r c • e x)
      (g : Module.End F V) (g' : Module.End F' V'), (∀ x, e (g x) = g' (e x)) →
      GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s' n V' g' = GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rw [GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, charpoly_semi r e he g g' hg, hs]
    congr 1
    have htop : smapE r e he ⊤ = ⊤ := by
      ext y
      change y ∈ smap r e he ⊤ ↔ _
      rw [mem_smap]
      simp
    have hsymm : ∀ y, e.symm (g' y) = g (e.symm y) := by
      intro y
      apply e.injective
      rw [hg]
      simp
    have hiff : ∀ W : Submodule F V, (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) ↔
        (smapE r e he W ≠ ⊤ ∧ ∀ y ∈ smapE r e he W, g' y ∈ smapE r e he W) := by
      intro W
      constructor
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · intro h
          apply hW
          apply (smapE r e he).injective
          rw [h, htop]
        · intro y hy
          change g' y ∈ smap r e he W
          change y ∈ smap r e he W at hy
          rw [mem_smap] at hy ⊢
          rw [hsymm]
          exact hinv _ hy
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hW htop
        · intro x hx
          have h1 : e x ∈ smap r e he W := by
            rw [mem_smap]
            simpa using hx
          have h2 := hinv (e x) h1
          change g' (e x) ∈ smap r e he W at h2
          rw [mem_smap, hsymm] at h2
          simpa using h2
    symm
    apply finsum_eq_of_bijective ((smapE r e he).subtypeEquiv hiff) (Equiv.bijective _)
    intro W
    symm
    exact ih _ _ (eRes r e he W.1)
      (by
        intro c x
        apply Subtype.ext
        simp [eRes, he])
      _ _
      (by
        intro x
        apply Subtype.ext
        simp [eRes, hg]
        rfl)

private theorem rootSum_iso {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
    (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ) (c : ℕ) (P : F[X]) :
    GlobalTheory.CuspGL.rootSum θ c (P.map r.toRingHom) = GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c P := by
  unfold GlobalTheory.CuspGL.rootSum
  have hpoly : (P.map r.toRingHom).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map j.toRingHom := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext x
    exact (hj x).symm
  rw [hpoly, ← roots_map_of_injective_of_card_eq_natDegree j.injective IsAlgClosed.card_roots_eq_natDegree,
    Multiset.map_map]
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.cuspIso :
    CuspIso := by
  intro F F' _ _ _ r j hj θ m c g
  unfold cusp psiG GlobalTheory.CuspGL.psi
  congr 1
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
  apply semilinear_equiv_conjugate_endomorphism r (GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c) (GlobalTheory.CuspGL.rootSum θ c)
    (rootSum_iso r j hj θ c) (m + 1) (Fin m → F) (Fin m → F') (AddEquiv.piCongrRight fun _ => r.toAddEquiv)
  · intro a x
    funext i
    simp
  · intro x
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFrobL
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons_of {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b : ℕ) (h : (Y.map Sigma.fst).sum = b) (n : ℕ) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h
  exact hcL_cons p Y n

private theorem collapse {G X Z : Type} [Finite G] [Finite X] [Finite Z]
    (A : G → Prop) (B : Z → Prop) (I : G → Prop) (tl : G → X) (br : G → Z)
    (hA : ∀ p, A p ↔ I p ∧ B (br p))
    (u : X → ℂ) (v : Subtype B → ℂ) (T : G → ℂ) (w : Subtype A → ℂ)
    (hw : ∀ p (hp : A p) (hp' : B (br p)), w ⟨p, hp⟩ = u (tl p) * v ⟨br p, hp'⟩) :
    ∑ᶠ x, u x * ∑ᶠ p' : Subtype B, v p' * (∑ᶠ p : G, if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0) =
      ∑ᶠ p : Subtype A, w p * T p := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Z
  have key : ∀ p : G, (∑ x, ∑ p' : Subtype B,
      u x * (v p' * if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0)) =
      if h : A p then w ⟨p, h⟩ * T p else 0 := by
    intro p
    by_cases hI : I p
    · by_cases hB : B (br p)
      · have hAp : A p := (hA p).2 ⟨hI, hB⟩
        rw [dif_pos hAp, hw p hAp hB, Fintype.sum_eq_single (tl p), Fintype.sum_eq_single ⟨br p, hB⟩]
        · simp [hI]
          ring
        · intro q hq
          rw [if_neg]
          · simp
          · rintro ⟨_, _, h⟩
            exact hq (Subtype.ext h.symm)
        · intro x hx
          apply Finset.sum_eq_zero
          intro q _
          rw [if_neg]
          · simp
          · rintro ⟨_, h, _⟩
            exact hx h.symm
      · rw [dif_neg (fun h => hB ((hA p).1 h).2)]
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg]
        · simp
        · rintro ⟨_, _, h⟩
          exact hB (h ▸ q.2)
    · rw [dif_neg (fun h => hI ((hA p).1 h).1)]
      simp [hI]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ => key p, ← Fintype.sum_subtype_add_sum_subtype A,
    Finset.sum_congr rfl fun p _ => dif_pos p.2,
    Finset.sum_congr rfl (fun (p : {p // ¬A p}) _ => dif_neg p.2), Finset.sum_const_zero, add_zero]

theorem UpperTheory.Gal.InertialTypesAlt.frobL :
    FrobTwo → ResCl → ParCons → FrobL := by
  intro hF2 hRes hPar F _ _ s
  induction s with
  | zero =>
    intro d n hd
    refine ⟨1, one_ne_zero, fun Y T _ => ?_⟩
    have hn : n = 0 := by rw [← hd]; simp
    subst hn
    have hall : ∀ g : GL (Fin 0) F, g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd) :=
      fun g => GlobalTheory.SmGL.mem_parab_iff.2 fun a => a.elim0
    simp only [List.ofFn_zero, hcL_nil, star_one, one_mul, Fin.prod_univ_zero]
    exact (finsum_comp_equiv (Equiv.subtypeUnivEquiv hall)).symm
  | succ s ih =>
    intro d n hd
    have hn : n = d 0 + ∑ i : Fin s, d i.succ := by rw [← hd, Fin.sum_univ_succ]
    obtain ⟨c1, hc1, h1⟩ := hF2 F (d 0) (∑ i : Fin s, d i.succ) n hn
    obtain ⟨c2, hc2, h2⟩ := ih (fun i => d i.succ) _ rfl
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, fun Y T hT => ?_⟩
    have htail : (List.map Sigma.fst (List.ofFn fun i : Fin s =>
        (⟨d i.succ, Y i.succ⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).sum = ∑ i : Fin s, d i.succ := by
      simp [List.sum_ofFn]
    rw [List.ofFn_succ, hcL_cons_of _ _ _ htail, h1 _ _ T hT]
    have h2' := fun x => h2 (fun i => Y i.succ) _ (hRes F _ _ n hn T hT x)
    rw [finsum_congr fun x => by rw [h2' x, mul_left_comm], ← mul_finsum, ← mul_assoc]
    clear h1 h2 h2' ih htail hF2 hRes
    refine congrArg (c1 * c2 * ·) ?_
    unfold UpperTheory.Gal.InertialTypesAlt.resT
    have hc := collapse (fun p => p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd))
      (fun z => z ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl))
      (GlobalTheory.Shin.InPar (d 0)) (GlobalTheory.Shin.tlG (d 0)) (GlobalTheory.Shin.brG (d 0) _)
      (fun p => (hPar F s n d hd _ rfl p).1) (fun x => star (Y 0 x))
      (fun p' => star (∏ i, Y i.succ (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl) p' i)))
      T (fun p => star (∏ i, Y i (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks d hd) p i))) (by
        intro p hp hp'
        obtain ⟨h0, hs⟩ := (hPar F s n d hd _ rfl p).2 hp hp'
        rw [Fin.prod_univ_succ, h0, star_mul']
        congr 2
        exact Finset.prod_congr rfl fun i _ => by rw [hs i])
    convert hc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFrobTwo
section
noncomputable section

open GlobalTheory.Shin
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt

private theorem gal_id {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

private theorem inPar_one {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [Matrix.one_apply_ne hij]

theorem frobTwo : FrobTwo := by
  intro F _ _ a b n _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
  have hN : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    haveI : Nonempty {p : GL (Fin n) F // InPar a p} := ⟨⟨1, inPar_one a n⟩⟩
    exact_mod_cast (Nat.card_pos (α := {p : GL (Fin n) F // InPar a p})).ne'
  have hG : (Fintype.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * (Fintype.card (GL (Fin n) F) : ℂ),
    mul_ne_zero (star_ne_zero.2 (inv_ne_zero hN)) hG, ?_⟩
  intro α β T hT
  set w : GL (Fin n) F → ℂ := fun p =>
    if InPar a p then star (α (tlG a p) * β (brG a b p)) * T p else 0 with hw
  have hleft : ∑ᶠ g, star (hc a b α β n g) * T g =
      star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) *
        ((Fintype.card (GL (Fin n) F) : ℂ) * ∑ p, w p) := by
    have hy : ∀ y : GL (Fin n) F,
        ∑ g : GL (Fin n) F, star (if InPar a (y⁻¹ * (g * y)) then
          α (tlG a (y⁻¹ * (g * y))) * β (brG a b (y⁻¹ * (g * y))) else 0) * T g = ∑ p, w p := by
      intro y
      refine Fintype.sum_equiv ((Equiv.mulRight y).trans (Equiv.mulLeft y⁻¹)) _ _ fun g => ?_
      have hTg : T (y⁻¹ * (g * y)) = T g := by
        rw [← mul_assoc]
        exact hT g y
      simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hw, hTg]
      split_ifs <;> simp
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype, star_mul', star_sum, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hright : ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y = ∑ p, w p := by
    have key : ∀ p : GL (Fin n) F, ∑ x : GL (Fin a) F, ∑ y : GL (Fin b) F,
        star (α x) * (star (β y) *
          if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0) = w p := by
      intro p
      rw [Finset.sum_eq_single (tlG a p), Finset.sum_eq_single (brG a b p)]
      · by_cases h : InPar a p <;> simp [hw, h, star_mul', mul_assoc]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    simp only [resT, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [← Finset.sum_congr rfl fun p _ => key p]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  rw [hleft, hright, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PKillsNil
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem frob_ne_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hp : (Module.finrank F F').Prime) (hs : ∀ z, s z = z ^ Nat.card F) :
    s ≠ 1 := by
  rintro rfl
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Fintype F' := Fintype.ofFinite F'
  have hcard : Nat.card F' = Nat.card F ^ Module.finrank F F' := Module.natCard_eq_pow_finrank
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hs hq hcard
  have hne : (X ^ q - X : F'[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hdeg : (X ^ q - X : F'[X]).natDegree = q := Polynomial.natDegree_X_pow_sub_X (R := F') hq
  have hsub : (Finset.univ : Finset F') ⊆ (X ^ q - X : F'[X]).roots.toFinset := by
    intro z _
    rw [Multiset.mem_toFinset, mem_roots hne]
    have := hs z
    simp only [AlgEquiv.one_apply] at this
    simp [IsRoot, ← this]
  have h1 : Nat.card F' ≤ q := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ Multiset.card (X ^ q - X : F'[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : F'[X]).natDegree := card_roots' _
      _ = q := hdeg
  rw [hcard] at h1
  have h2 : q ^ 2 ≤ q ^ Module.finrank F F' := Nat.pow_le_pow_right (by omega) hp.two_le
  nlinarith

theorem UpperTheory.Gal.InertialTypesAlt.killsNil :
    KillsAll → KillsOn fun a => a.D = [] := by
  intro h F F' _ _ _ _ s hp hs ι θ hθ a hD hok hq
  obtain ⟨q, D, L⟩ := a
  simp only at hD hq
  subst hD
  subst hq
  have key := h F F' s hp (frob_ne_one s hp hs) ι θ hθ L (fun p hp' => hok.2.2 p hp') (deg L) rfl
  have hrk : (⟨Nat.card F, [], L⟩ : Lbl).rk = deg L := by
    have h0 : GlobalTheory.Shin.deg ([] : List (ℕ × ℕ)) = 0 := rfl
    simp [Lbl.rk, h0]
  rw [hrk]
  simpa [Lbl.lift, JD_nil] using key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftsFix
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.liftsFix :
    LiftsFix := by
  intro E Ω _ _ _ n X Y h x
  induction h with
  | refl => exact ⟨x, rfl⟩
  | @tail B C _ hs ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨i₁, i₂, -⟩ := hs
    refine ⟨algebraMap B.K C.K y, ?_⟩
    rw [← hy]
    exact (IsScalarTower.algebraMap_apply B.K C.K Ω y).symm
end

