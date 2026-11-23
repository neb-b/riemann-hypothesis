module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0020

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.OpenCovPtaPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.OpenCov_ptaPf

variable (R : Type) [CommRing R]

abbrev gen (P : PSh) {W : Scheme.{0}ᵒᵖ} (x : P.obj W) : ((freeP R).obj P).obj W :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj W)) (ULift.up x)

abbrev adj {P : PSh} {G : Shv R} (a : (free R).obj P ⟶ G) : (freeP R).obj P ⟶ G.obj :=
  toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ a.hom

theorem adj_inj {P : PSh} {G : Shv R} (a b : (free R).obj P ⟶ G) (h : adj R a = adj R b) : a = b := by
  ext1
  exact sheafify_hom_ext _ _ _ G.property h

theorem adj_comp {P Q : PSh} {G : Shv R} (φ : P ⟶ Q) (a : (free R).obj Q ⟶ G) :
    adj R ((free R).map φ ≫ a) = (freeP R).map φ ≫ adj R a := by
  show toSheafify _ _ ≫ (sheafifyMap _ ((freeP R).map φ) ≫ a.hom) = _
  show _ = (freeP R).map φ ≫ toSheafify _ _ ≫ a.hom
  erw [toSheafify_naturality_assoc]

theorem freePresheaf_obj_map_freeMk (P : PSh) {W W' : Scheme.{0}ᵒᵖ} (h : W ⟶ W') (x : P.obj W) :
    ((freeP R).obj P).map h (gen R P x) = gen R P (P.map h x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem freePresheaf_map_freeMk {P Q : PSh} (φ : P ⟶ Q) (W : Scheme.{0}ᵒᵖ) (x : P.obj W) :
    ((freeP R).map φ).app W (gen R P x) = gen R Q (φ.app W x) := by
  dsimp [freeP, gen]
  erw [ModuleCat.free_map_apply]
  rfl

theorem adj_val {X Y : Scheme.{0}} {G : Shv R} (a : (free R).obj (yoneda.obj X) ⟶ G) (x : Y ⟶ X) :
    (adj R a).app (op Y) (gen R (yoneda.obj X) (W := op Y) x) =
      G.obj.map x.op ((adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X))) := by
  rw [← ConcreteCategory.comp_apply, ← (adj R a).naturality, ConcreteCategory.comp_apply, freePresheaf_obj_map_freeMk]
  simp

theorem ext_of_cover {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hcov : Set.range f ∪ Set.range g = Set.univ) {G : Shv R} (a b : (free R).obj (yoneda.obj X) ⟶ G)
    (hf : (free R).map (yoneda.map f) ≫ a = (free R).map (yoneda.map f) ≫ b)
    (hg : (free R).map (yoneda.map g) ≫ a = (free R).map (yoneda.map g) ≫ b) : a = b := by
  let Z : Bool → Scheme.{0} := fun i => Bool.rec V U i
  let φ : ∀ i, Z i ⟶ X := fun i => Bool.rec (motive := fun i => Z i ⟶ X) g f i
  have hS : Sieve.ofArrows Z φ ∈ Scheme.etaleTopology X := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : x ∈ Set.range f ∪ Set.range g := hcov ▸ Set.mem_univ x
      rcases hx with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · cases i <;> infer_instance
  have hf' := congrArg (adj R) hf
  have hg' := congrArg (adj R) hg
  rw [adj_comp, adj_comp] at hf' hg'
  have key : (adj R a).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) =
      (adj R b).app (op X) (gen R (yoneda.obj X) (W := op X) (𝟙 X)) := by
    refine Presheaf.IsSheaf.isSeparated G.property _ _ hS _ _ ?_
    intro Y' h hh
    obtain ⟨W, k, _, ⟨i⟩, rfl⟩ := hh
    rw [← adj_val, ← adj_val]
    cases i
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj V) (W := op _) k)) hg'
      simpa [freePresheaf_map_freeMk] using this
    · have := congrArg (fun t => t.app (op _) (gen R (yoneda.obj U) (W := op _) k)) hf'
      simpa [freePresheaf_map_freeMk] using this
  apply adj_inj
  ext Y : 2
  induction Y with | op Y => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact (adj_val R a x).trans ((congrArg _ key).trans (adj_val R b x).symm)

theorem openCov : LateralTheory.E.MayerVietorisSequence.OpenCov := by
  intro R _ U V X f g _ _ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance
  have : sch.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  refine ⟨inferInstance, inferInstance, fun n => ⟨fun {G} a b h => ?_⟩⟩
  apply ext_of_cover R f g hcov a b
  · have h1 : (free R).map ((sch.map f).app n) ≫ a = (free R).map ((sch.map f).app n) ≫ b := by
      simpa using congrArg (biprod.inl ≫ ·) h
    exact h1
  · have h1 : (free R).map ((sch.map g).app n) ≫ a = (free R).map ((sch.map g).app n) ≫ b := by
      simpa using congrArg (biprod.inr ≫ ·) h
    exact h1

end LateralTheory.E.OpenCov_ptaPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PrimitiveRootLocalization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.PrimitiveRootLocalization

theorem cyc_cond {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ (p₁ p₂ : A[X]) (n : ℕ), derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = (1 : A[X]) ^ n := by
  obtain ⟨h, e1⟩ := cyclotomic.dvd_X_pow_sub_one q A
  obtain ⟨v, hv⟩ := hq.exists_left_inv
  have e2 := congrArg derivative e1
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at e2
  have e3 : C v * C (q : A) = 1 := by rw [← C_mul, hv, C_1]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have e4 : X * X ^ (q - 1) = (X : A[X]) ^ q := by rw [← pow_succ']; congr 1; omega
  refine ⟨C v * X * h, C v * X * derivative h - h, 0, ?_⟩
  linear_combination (-(C v * X)) * e2 + (C v * C (q : A)) * e4 + X ^ q * e3 + e1

def cycPair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := cyc_cond q hq

section
variable {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A))

theorem cycPair_hasMap_root : (cycPair q hq).HasMap (AdjoinRoot.root (cyclotomic q A)) := by
  refine ⟨?_, ?_⟩
  · simp [cycPair]
  · simp [cycPair]

theorem adjoinRoot_nontrivial [Nontrivial A] : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h1 := (cyclotomic.monic q A).isUnit_iff.mp hu
  have h2 := natDegree_cyclotomic q A
  rw [h1, natDegree_one] at h2
  exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne' h2.symm

theorem comap_surj : Function.Surjective (PrimeSpectrum.comap (algebraMap A (cycPair q hq).Ring)) := by
  by_cases hA : Nontrivial A
  · let ψ : (cycPair q hq).Ring →ₐ[A] AdjoinRoot (cyclotomic q A) := (cycPair q hq).lift _ (cycPair_hasMap_root q hq)
    have := (cyclotomic.monic q A).free_adjoinRoot
    have := adjoinRoot_nontrivial (A := A) q
    have hs := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := AdjoinRoot (cyclotomic q A))
    have e : algebraMap A (AdjoinRoot (cyclotomic q A)) = (ψ : (cycPair q hq).Ring →+* _).comp (algebraMap A (cycPair q hq).Ring) := by
      ext a; simp
    intro x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨PrimeSpectrum.comap (ψ : (cycPair q hq).Ring →+* _) y, ?_⟩
    rw [← hy, e]
    rfl
  · intro x
    rw [not_nontrivial_iff_subsingleton] at hA
    exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

def primRing : Prim q (cycPair q hq).Ring :=
  ⟨(cycPair q hq).X, by simpa using hq.map (algebraMap A (cycPair q hq).Ring), by
    have h := (cycPair q hq).hasMap_X.1
    change aeval (cycPair q hq).X (cyclotomic q A) = 0 at h
    rw [← map_cyclotomic q (algebraMap ℤ A), aeval_map_algebraMap] at h
    exact h⟩

end

theorem LeafPrimLoc_of : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := by
  intro q _ U hq
  let P := cycPair (A := Γ(U, ⊤)) q hq
  let f : Spec (CommRingCat.of P.Ring) ⟶ Spec Γ(U, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) P.Ring))
  have hfe : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hfs : Surjective f := ⟨comap_surj q hq⟩
  have hge : Etale (pullback.fst U.toSpecΓ f) := inferInstance
  have hgs : Surjective (pullback.fst U.toSpecΓ f) := inferInstance
  let S : Sieve U :=
    { arrows := fun V _ => Nonempty (Prim q Γ(V, ⊤))
      downward_closed := fun {V W} g hg h => hg.elim fun ζ => ⟨Prim.map h.appTop.hom ζ⟩ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨hgs.surj, hge⟩))
  rintro V _ ⟨W, h, k, ⟨⟩, rfl⟩
  exact ⟨Prim.map ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv ≫ (h ≫ pullback.snd _ _).appTop).hom (primRing q hq)⟩

end LateralTheory.E.PrimitiveRootLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.ProEqvPf

def fm {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (u : U ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of A)) :
    pullback (u ≫ g) (cpt A) ⟶ pullback g (cpt A) :=
  pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by simp) (by simp)

def Hit (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) : Prop :=
  ∃ w : Ht q (sch.obj U) n i, pull _ (sch.map (pullback.fst (u ≫ g) (cpt A))) _ _ w = pull _ (sch.map (fm u g)) _ _ z

def PiLocalization₂ : Prop := LateralTheory.E.t_E2Cut.Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∃ j, pull _ (sch.map (ι j)) _ _ x = 0) ∧
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

def Glue : Prop := MV → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (n : ℤ),
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ pull _ (sch.map u) _ _ x = 0) →
  (∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ Hit q i n g z u) →
  Function.Bijective (pull _ (sch.map (pullback.fst g (cpt A))) (tw q i) n)

theorem ProEqv_of (hC : LateralTheory.E.t_E2Cut.Cont) (hM : MV) (hS : PiLocalization₂) (hG : Glue) : ProEqv := by
  intro H q i A _ _ hq Y _ _ g hY n
  refine hG hM H q i A hq g n (fun x hx y => ?_) (fun z y => ?_)
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).1 x hx
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).2 z
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩

end LateralTheory.E.ProEqvPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProdAcycPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ProdAcycPf

theorem zero_acyc (H : LateralTheory.E.t_E2Cut.Hyp) (q : ℕ) (A : Type) [CommRing A] [Subsingleton A] : Acyc q (sp A) := by
  intro n i hn
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : Ht q (sp A) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, -, -, hx⟩ := H.a5 (ZMod q) (Spec (CommRingCat.of A)) (tw q i) n hn x
    have : IsEmpty (Spec (CommRingCat.of A)) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    have : IsIso (sch.map f) := inferInstance
    have hy : pull _ (inv (sch.map f)) _ _ (pull _ (sch.map f) _ _ x) = x := by
      rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    rw [← hy, hx, map_zero]
  rw [h0 x, h0 y]

def Bin : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1],
  Nonempty (A ≃+* R0 × R1) → Acyc q (sp R0) → Acyc q (sp R1) → Acyc q (sp A)

def splitFirst (n : ℕ) (R : Fin (n + 1) → Type) [∀ k, CommRing (R k)] :
    (∀ k, R k) ≃+* R 0 × ∀ k : Fin n, R k.succ where
  toFun f := (f 0, fun k => f k.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem prod_of (hB : Bin) : LateralTheory.E.QuotAcycCut.ProdAcyc := by
  intro H q A _ n
  induction n generalizing A with
  | zero =>
    intro R _ ⟨e⟩ _
    have : Subsingleton A := e.injective.subsingleton
    exact zero_acyc H q A
  | succ n ih =>
    intro R _ ⟨e⟩ hR
    refine hB H q A (R 0) (∀ k : Fin n, R k.succ) ⟨e.trans (splitFirst n R)⟩ (hR 0) ?_
    exact ih (∀ k : Fin n, R k.succ) (fun k => R k.succ) ⟨RingEquiv.refl _⟩ fun k => hR k.succ

end LateralTheory.E.ProdAcycPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProjFPf
section
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjFPf

section Tw
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

theorem twist_apply (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

def tinv (ε : ZMod q → A) (z : ZMod q → A) : ZMod q → A := fun k => ∑ d, ε (-d) * z (k + d)

theorem twist_tinv (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : twist hε (tinv ε z) = z := by
  funext k
  rw [twist_apply]
  unfold tinv
  have : ∀ c, ε c * ∑ d, ε (-d) * z (k + c + d) = ε c * z k := by
    intro c
    rw [Finset.mul_sum, Finset.sum_eq_single (-c)]
    · rw [neg_neg, ← mul_assoc, (hε.idem c).eq, add_neg_cancel_right]
    · intro d _ hd
      have : c ≠ -d := fun h => hd (by rw [h, neg_neg])
      rw [← mul_assoc, hε.ortho this, zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul, hε.complete, one_mul]

theorem tinv_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : tinv ε (twist hε z) = z := by
  funext k
  unfold tinv
  simp_rw [twist_apply]
  have : ∀ d, ε (-d) * ∑ c, ε c * z (k + d + c) = ε (-d) * z k := by
    intro d
    rw [Finset.mul_sum, Finset.sum_eq_single (-d)]
    · rw [← mul_assoc, (hε.idem (-d)).eq, add_neg_cancel_right]
    · intro c _ hc
      rw [← mul_assoc, hε.ortho (Ne.symm hc), zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul]
  rw [show (∑ d : ZMod q, ε (-d)) = ∑ d, ε d from
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl), hε.complete, one_mul]

theorem twist_const_mul (hε : CompleteOrthogonalIdempotents ε) (a : A) (z : ZMod q → A) :
    twist hε (fun k => a * z k) = fun k => a * twist hε z k := by
  funext k
  simp only [twist_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem eq_zero_of_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (h : twist hε z = 0) : z = 0 := by
  rw [← tinv_twist hε z, h]; funext k; simp [tinv]
end Tw

section Main
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S)

theorem mem_tor {ε : ZMod q → Localization.Away (f * g)} (hε : CompleteOrthogonalIdempotents ε) (p : Amb f g q) :
    p ∈ Tor f g hε ↔ ∀ k, rL f g (p.1 k) = twist hε (fun j => rR f g (p.2 j)) k :=
  funext_iff

theorem rR_alg (a : S) : rR f g (algebraMap S (Localization.Away g) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rR; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_alg (a : S) : rL f g (algebraMap S (Localization.Away f) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rL; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem unit_g : IsUnit (algebraMap S (Localization.Away (f * g)) g) := by
  refine isUnit_of_mul_isUnit_right (x := algebraMap S (Localization.Away (f * g)) f) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g)

theorem kill (z : Localization.Away g) (hz : rR f g z = 0) :
    ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * z = 0 := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
  dsimp only at hz ⊢
  have hb : algebraMap S (Localization.Away (f * g)) b = 0 := by
    rw [← rR_alg, ← IsLocalization.mk'_spec (Localization.Away g) b s, map_mul, hz, zero_mul]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ b).mp hb
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n)) :=
    (IsLocalization.map_units (Localization.Away g) s).mul
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n)
  refine (hu.mul_left_eq_zero).mp ?_
  calc algebraMap S (Localization.Away g) f ^ n * IsLocalization.mk' (Localization.Away g) b s *
        (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n))
      = algebraMap S (Localization.Away g) f ^ n *
        (IsLocalization.mk' (Localization.Away g) b s * algebraMap S (Localization.Away g) (s : S)) *
        algebraMap S (Localization.Away g) (g ^ n) := by ring
    _ = algebraMap S (Localization.Away g) ((f * g) ^ n * b) := by
        rw [IsLocalization.mk'_spec, mul_pow]; simp only [map_mul, map_pow]; ring
    _ = 0 := by simp only at hn; rw [hn, map_zero]
end Main

theorem projF : ProjF := by
  intro q _ S _ f g _ ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr1 f g hε).toAlgebra
  have hA : ∀ t : Tor f g hε, algebraMap (Tor f g hε) (ZMod q → Localization.Away f) t = (t : Amb f g q).1 :=
    fun _ => rfl
  have hf : algebraMap S (Tor f g hε) f = torMap f g hε f := rfl
  have hT1 : ((torMap f g hε f : Tor f g hε) : Amb f g q).1 = fun _ => algebraMap S (Localization.Away f) f := rfl
  have hT2 : ((torMap f g hε f : Tor f g hε) : Amb f g q).2 = fun _ => algebraMap S (Localization.Away g) f := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hA, hf, hT1, Pi.isUnit_iff]; intro _; exact IsLocalization.Away.algebraMap_isUnit f
  · intro s
    set w : ZMod q → Localization.Away (f * g) := tinv ε (fun k => rL f g (s k)) with hw
    obtain ⟨⟨_, n, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
    have hb' : ∀ i, ∃ a, algebraMap S (Localization.Away (f * g)) a = (f * g) ^ n • w i :=
      fun i => RingHom.mem_rangeS.mp (hb i)
    choose a ha using hb'
    let y : ZMod q → Localization.Away g := fun k =>
      IsLocalization.mk' (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    have hy : ∀ k, rR f g (y k) = algebraMap S _ (f ^ n) * w k := by
      intro k
      have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (g ^ n)) := by
        rw [map_pow]; exact (unit_g f g).pow n
      apply hu.mul_left_injective
      have e1 := IsLocalization.mk'_spec (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
      simp only at e1 ⊢
      rw [← rR_alg f g (g ^ n), ← map_mul, e1]
      simp only [rR_alg, ha k, Algebra.smul_def, mul_pow, map_mul, map_pow]
      ring
    let x : ZMod q → Localization.Away f := fun k => s k * algebraMap S _ f ^ n
    have hmem : ((x, y) : Amb f g q) ∈ Tor f g hε := by
      rw [mem_tor]; intro k
      have h2 : (fun j => rR f g (((x, y) : Amb f g q).2 j)) = fun j => algebraMap S _ (f ^ n) * w j := funext hy
      rw [h2, twist_const_mul, hw, twist_tinv]
      show rL f g (s k * algebraMap S _ f ^ n) = _
      rw [map_mul, map_pow, rL_alg, map_pow]; ring
    refine ⟨n, ⟨(x, y), hmem⟩, ?_⟩
    show s * (((torMap f g hε f : Tor f g hε) : Amb f g q).1) ^ n = x
    rw [hT1]
    funext k
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  · intro a b hab
    have hc1 : ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by
      rw [← hA (a - b), map_sub, hab, sub_self]
    have hm := (mem_tor f g hε _).mp (a - b).2
    have htw : twist hε (fun j => rR f g (((a - b : Tor f g hε) : Amb f g q).2 j)) = 0 := by
      funext k; rw [← hm k, hc1]; simp
    have hc2 := eq_zero_of_twist hε _ htw
    have hk : ∀ k, ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * ((a - b : Tor f g hε) : Amb f g q).2 k = 0 :=
      fun k => kill f g _ (congrFun hc2 k)
    choose m hm' using hk
    refine ⟨Finset.univ.sup m, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    apply Subtype.ext
    apply Prod.ext
    · have e : ((algebraMap S (Tor f g hε) f ^ Finset.univ.sup m : Tor f g hε) : Amb f g q).1 *
          ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by rw [hc1, mul_zero]
      exact e
    · funext k
      show (algebraMap S (Localization.Away g) f) ^ (Finset.univ.sup m) * ((a - b : Tor f g hε) : Amb f g q).2 k = 0
      rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : m k ≤ Finset.univ.sup m), pow_add, mul_assoc, hm' k,
        mul_zero]

end LateralTheory.E.ProjFPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SepTensorPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SepTensorPf

theorem SepTensor_of : LateralTheory.E.SHTensorPf.SepTensor := by
  intro A X B Z x b u v hp _ hX _ hb _ hZ
  obtain ⟨_, hXs⟩ := hX
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  let f : X →+* IsLocalRing.ResidueField Z := (IsLocalRing.residue Z).comp u.hom
  have hf : f.IsIntegral := RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu
    (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)
  let _ : Algebra X (IsLocalRing.ResidueField Z) := f.toAlgebra
  have : Algebra.IsIntegral X (IsLocalRing.ResidueField Z) := ⟨hf⟩
  have : Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z) :=
    Algebra.IsIntegral.tower_top X
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)

end LateralTheory.E.SepTensorPf
end
end

