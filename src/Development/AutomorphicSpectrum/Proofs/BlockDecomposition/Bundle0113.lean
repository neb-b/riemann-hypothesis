module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneSubPow
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimAlgProof

open Polynomial

theorem exists_universal (q : ℕ) [NeZero q] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (ξ : R), IsPrimitiveRoot ξ q ∧
      ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
        ∃ φ : R →+* A, φ ξ = z := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlift : ∀ (A : Type) [CommRing A] (z : A), aeval z (cyclotomic q ℤ) = 0 →
      ∃ φ : AdjoinRoot (cyclotomic q ℤ) →+* A, φ (AdjoinRoot.root _) = z := by
    intro A _ z hz
    have h : (cyclotomic q ℤ).eval₂ (Int.castRingHom A) z = 0 := by
      rw [aeval_def] at hz
      simpa [eq_intCast] using hz
    exact ⟨AdjoinRoot.lift _ z h, AdjoinRoot.lift_root h⟩
  haveI hdom : IsDomain (AdjoinRoot (cyclotomic q ℤ)) :=
    AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hq).prime
  refine ⟨AdjoinRoot (cyclotomic q ℤ), inferInstance, hdom, AdjoinRoot.root _, ?_, hlift⟩
  obtain ⟨ψ, hψ⟩ := hlift ℂ (Complex.exp (2 * Real.pi * Complex.I / q)) (by
    have hp := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
    have : IsRoot (cyclotomic q ℂ) (Complex.exp (2 * Real.pi * Complex.I / q)) :=
      (isRoot_cyclotomic_iff).2 hp
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact this)
  haveI : NeZero ((q : ℕ) : AdjoinRoot (cyclotomic q ℤ)) := ⟨fun h0 => by
    have := congrArg ψ h0
    rw [map_natCast, map_zero] at this
    exact NeZero.ne q (by exact_mod_cast this)⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  have h := AdjoinRoot.eval₂_root (cyclotomic q ℤ)
  rw [eval₂_eq_eval_map, map_cyclotomic] at h
  exact h

theorem X_pow_sub_one_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    (X ^ q - 1 : R[X]) = ∏ a : ZMod q, (X - C (ξ ^ a.val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [X_pow_sub_one_eq_prod hq hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ a.val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_nthRootsFinset hq]
    rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  · intro a _ b _ h
    exact ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  · intro μ hμ
    rw [mem_nthRootsFinset hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ
    exact ⟨(i : ZMod q), Finset.mem_univ _, by rw [ZMod.val_cast_of_lt hi]⟩
  · intro a _
    rfl

theorem cyclotomic_eq {R : Type} [CommRing R] [IsDomain R] (q : ℕ) [NeZero q] {ξ : R}
    (hξ : IsPrimitiveRoot ξ q) :
    cyclotomic q R = ∏ a : (ZMod q)ˣ, (X - C (ξ ^ (a : ZMod q).val)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hξ]
  symm
  refine Finset.prod_bij (fun a _ => ξ ^ (a : ZMod q).val) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_primitiveRoots hq]
    exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  · intro a _ b _ h
    exact Units.ext (ZMod.val_injective q (hξ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  · intro μ hμ
    rw [mem_primitiveRoots hq] at hμ
    obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    have hc : Nat.Coprime i q := (hξ.pow_iff_coprime hq i).1 hμ
    refine ⟨ZMod.unitOfCoprime i hc, Finset.mem_univ _, ?_⟩
    simp only [ZMod.coe_unitOfCoprime]
    rw [ZMod.val_cast_of_lt hi]
  · intro a _
    rfl

theorem isUnit_one_sub_pow {R A : Type} [CommRing R] [IsDomain R] [CommRing A] (n : ℕ) {ξ : R}
    (hξ : IsPrimitiveRoot ξ (n + 1)) (φ : R →+* A) (hu : IsUnit ((n + 1 : ℕ) : A))
    (k : ℕ) (hk : k < n) : IsUnit (1 - φ ξ ^ (k + 1)) := by
  have h := congrArg φ hξ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  have hn : φ ((n : R) + 1) = ((n + 1 : ℕ) : A) := by simp
  have hd : φ (1 - ξ ^ (k + 1)) ∣ ∏ i ∈ Finset.range n, φ (1 - ξ ^ (i + 1)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)
  rw [h, hn] at hd
  have := isUnit_of_dvd_unit hd hu
  simpa using this

theorem primAlg : CrystallineSemistableComparison.E.PrimAlg := by
  intro q _ A _ ζ
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨R, _, _, ξ, hξ, hl⟩ := exists_universal q
  obtain ⟨φ, hφ⟩ := hl A ζ.1 ζ.2.2
  have hpow : ζ.1 ^ q = 1 := by rw [← hφ, ← map_pow, hξ.pow_eq_one, map_one]
  have hζu : IsUnit ζ.1 := by
    refine IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) ?_
    rw [← pow_succ', Nat.sub_add_cancel hq, hpow]
  have h1 : ∀ k, 0 < k → k < q → IsUnit (1 - ζ.1 ^ k) := by
    intro k hk0 hkq
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    subst hn
    have := isUnit_one_sub_pow n hξ φ ζ.2.1 m (by omega)
    rwa [hφ] at this
  have hlt : ∀ a b : ℕ, a < b → b < q → IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
    intro a b hab hb
    have : ζ.1 ^ a - ζ.1 ^ b = ζ.1 ^ a * (1 - ζ.1 ^ (b - a)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this]
    exact (hζu.pow a).mul (h1 _ (by omega) (by omega))
  refine ⟨hpow, ?_, ?_, ?_⟩
  · intro a b hab
    have hv : a.val ≠ b.val := fun h => hab (ZMod.val_injective q h)
    rcases lt_or_gt_of_ne hv with h | h
    · exact hlt _ _ h (ZMod.val_lt b)
    · have := (hlt _ _ h (ZMod.val_lt a)).neg
      rwa [neg_sub] at this
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (X_pow_sub_one_eq q hξ)
    simpa [Polynomial.map_prod, eval_prod, hφ] using h
  · intro r
    have h := congrArg (fun p => eval r (p.map φ)) (cyclotomic_eq q hξ)
    simp only [map_cyclotomic, Polynomial.map_prod, eval_prod] at h
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, h]
    simp [hφ]

end GlobalTheory.CompanionTheory.PrimAlgProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapSurjective
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapBij

section Res

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_smul {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a :=
  map_smul _ _ _

theorem res_res {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  show (F.obj.map k.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (k ≫ g).op).hom a
  rw [op_comp, F.obj.map_comp]
  rfl

end Res

theorem nsmul_eq_up {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ℕ) (t : M) :
    c • t = (ULift.up (c : ZMod q) : ULift.{1} (ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1

theorem coef_eq_zero (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = 0) : a = 0 := by
  have hq : q ∣ a.val := (hg q i).2.1 V ζ a.val (by
    rw [nsmul_eq_up (q := q), ZMod.natCast_zmod_val]
    exact h)
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.natCast_eq_zero_iff _ _).2 hq

theorem coef_unique (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a b : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = (ULift.up b : ULift.{1} (ZMod q)) • twGen i ζ) :
    a = b := by
  refine sub_eq_zero.1 (coef_eq_zero hg i ζ _ ?_)
  have e : (ULift.up (a - b) : ULift.{1} (ZMod q)) = ULift.up a - ULift.up b := rfl
  rw [e, sub_smul, h, sub_self]

theorem coef_agree (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) {V V' : Scheme.{0}} (g : V ⟶ U) (g' : V' ⟶ U)
    (c c' : ZMod q)
    (h : Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    (h' : Sec.res g' x = (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res g' (twGen i ζ))
    (v : V) (v' : V') (hv : g v = g' v') : c = c' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v v' hv
  have : Nonempty ↑(pullback g g') := ⟨z⟩
  have e1 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [← res_res, h, res_smul, res_res]
  have e2 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [pullback.condition, ← res_res, h', res_smul, res_res]
  rw [((hR q i U ζ).1 _ (pullback.fst g g' ≫ g)).1] at e1 e2
  exact coef_unique hg i _ c c' (e1.symm.trans e2)

theorem exists_chart (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) (u : U) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ u ∈ Set.range g ∧
      ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ) := by
  refine (loc_iff_etale_affine_points U
    (fun V g => ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    ?_).1 ?_ u
  · rintro V W g k ⟨c, hc⟩
    exact ⟨c, by rw [← res_res, hc, res_smul, res_res]⟩
  · obtain ⟨S, hS, hc⟩ := (hg q i).1 U ζ x
    refine ⟨S, hS, fun V g hgS => ?_⟩
    obtain ⟨c, hc⟩ := hc V g hgS
    refine ⟨(c : ZMod q), ?_⟩
    rw [hc, nsmul_eq_up (q := q), ((hR q i U ζ).1 V g).1]
    rfl

theorem kap_injective (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (kap i ζ) := by
  refine (injective_iff_map_eq_zero (kap i ζ)).2 fun f hf => LocallyConstant.ext fun u => ?_
  let O : U.Opens := ⟨f ⁻¹' {f u}, f.isLocallyConstant.isOpen_fiber _⟩
  have : Nonempty O.toScheme := ⟨⟨u, rfl⟩⟩
  have hO : ∀ v : O.toScheme, f (O.ι v) = f u := fun v => by
    have : O.ι v ∈ Set.range O.ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  have h := (hK q i U ζ f).1 O.toScheme O.ι (f u) hO
  rw [hf] at h
  have h0 : Sec.res O.ι (0 : Sec (tw q i) U) = 0 := map_zero _
  rw [h0] at h
  exact coef_eq_zero hg i _ _ h.symm

theorem kap_surjective (hR : RepRoot) (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Function.Surjective (kap i ζ) := by
  intro x
  choose V g hA hE hu c hc using exists_chart hR hg i ζ x
  choose y hy using hu
  have hagree : ∀ (u : U) (v : V u), c (g u v) = c u := fun u v =>
    coef_agree hR hg i ζ x (g (g u v)) (g u) _ _ (hc _) (hc u) (y _) v (hy _)
  have hop : ∀ u, IsOpen (Set.range (g u)) := fun u => by
    have := hE u
    exact (g u).isOpenMap.isOpen_range
  let f : LocallyConstant U (ZMod q) := ⟨c, (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (g u), hop u, ⟨y u, hy u⟩, by
      rintro _ ⟨v, rfl⟩
      exact hagree u v⟩⟩
  refine ⟨f, ((sec_ext_glue _ _ U).1 _ _ ?_)⟩
  refine (loc_iff_etale_affine_points U (fun V g => Sec.res g (kap i ζ f) = Sec.res g x) ?_).2 fun u => ?_
  · intro V W g k h
    rw [← res_res, h, res_res]
  · refine ⟨V u, g u, hA u, hE u, ⟨y u, hy u⟩, ?_⟩
    have h := (hK q i U ζ f).1 (V u) (g u) (c u) (hagree u)
    rw [h, hc u, ((hR q i U ζ).1 _ (g u)).1]

theorem kapBij : LcCover → RepRoot → KapSpec → KapBij := fun _ hR hK hg q _ i _ ζ =>
  ⟨kap_injective hK hg i ζ, kap_surjective hR hK hg i ζ⟩

end GlobalTheory.CompanionTheory.KapBij
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EtNatProof

def resHom {R : Type} [CommRing R] (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec G U →+ Sec G V :=
  (G.obj.map g.op).hom.toAddMonoidHom

theorem res_res {R : Type} [CommRing R] (G : Shv R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec G U) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  simp [Sec.res]

theorem res_map {R : Type} [CommRing R] {G G' : Shv R} (φ : G ⟶ G') {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun t => t.hom a) h).symm

theorem kap_zero (hKap : KapSpec) (hTw : TwZero) (hGen : InGen) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (ζ ξ : Prim q Γ(U, ⊤)) (f : LocallyConstant U (ZMod q)) : kap 0 ζ f = kap 0 ξ f := by
  refine ((hKap q 0 U ζ f).2.1 _ ?_).symm
  intro V g a hv
  rw [(hKap q 0 U ξ f).1 V g a hv, hTw hGen q V (primRes g ξ) (primRes g ζ)]

def resMor {q : ℕ} {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (P : Probe C q) (P' : Probe C' q)
    (m : Mor P.L P'.L (RingHom.id ℤ)) (g : ∀ c : C', P'.U c ⟶ P.U (m.G.obj c))
    (hg : ∀ {c c' : C'} (φ : c ⟶ c'), g c' ≫ (P.S.map (m.G.map φ)).unop = (P'.S.map φ).unop ≫ g c)
    (i : ℤ)
    (hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f)) :
    ResMor (P.res i) (P'.res i) m where
  τ s c := resHom _ (g c)
  nat s {c c'} φ x := by
    change Sec.res (g c') (Sec.res (P.S.map (m.G.map φ)).unop x) = Sec.res (P'.S.map φ).unop (Sec.res (g c) x)
    rw [res_res, res_res, hg φ]
  ι c x := by
    change Sec.res (g c) (Sec.map (resι _ (tw q i)) (kap i (P.ζ (m.G.obj c)) x)) =
      Sec.map (resι _ (tw q i)) (kap i (P'.ζ c) (m.τ c x))
    rw [res_map, hι]
  dv s c x := by
    change Sec.res (g c) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) x) =
      Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (Sec.res (g c) x)
    exact res_map _ _ _

theorem etNat : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.EdgeMap → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.TwZero → CrystallineSemistableComparison.E.EtNat := by
  intro hEt hEM hRep hKap hTw hGen q _ C C' _ _ P P' X X' Y Y' u m g hg hτ hy i hi j x
  obtain ⟨a, ha⟩ := (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).1 x
  have hE := (hEt hGen q C P X Y i j x).1 a ha
  have hι : ∀ (c : C') (f : LocallyConstant (P.U (m.G.obj c)) (ZMod q)),
      Sec.res (g c) (kap i (P.ζ (m.G.obj c)) f) = kap i (P'.ζ c) (m.τ c f) := by
    intro c f
    rw [(hKap q i _ (P.ζ (m.G.obj c)) f).2.2 _ (g c), hτ c f]
    rcases hi with rfl | hi
    · exact kap_zero hKap hTw hGen q _ _ _
    · rw [hi c]
  let n := resMor P P' m g hg i hι
  have hE' := hEM ℤ ℤ (RingHom.id ℤ) C C' P.L P'.L (P.res i) (P'.res i) m n j _ _ hE
  have hglob : n.pullC j 0 (Y.glob i j a) = Y'.glob i j (Sec.res u a) := by
    funext t
    change Sec.res (g (t.obj (Fin.last 0))) (Sec.res (Y.y (m.G.obj (t.obj (Fin.last 0)))) a) =
      Sec.res (Y'.y (t.obj (Fin.last 0))) (Sec.res u a)
    rw [res_res, res_res, hy]
  rw [hglob] at hE'
  have hR : Rep (pull _ (sch.map u) _ j x) (Sec.res u a) :=
    (hRep (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.2.2.2 X' u x a ha
  exact (hEt hGen q C' P' X' Y' i j _).2 _ ⟨_, hR, hE'⟩

end GlobalTheory.CompanionTheory.EtNatProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechLine

variable {X : Scheme.{0}} (D : LineData X)

theorem u_self {V : Scheme.{0}} (a : V ⟶ D.Y) (h : a ≫ D.f = a ≫ D.f) : D.u a a h = 1 := by
  have h2 : D.u a a h * D.u a a h = D.u a a h * 1 := by
    rw [mul_one]
    exact D.coc a a a h h
  exact mul_left_cancel h2

theorem u_congr {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha
  subst hb
  rfl

def lineFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ D.Y)) (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) :
    ComposableArrows (SingleObj (GL (Fin 1) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j))
  map_id i := by rw [u_self]; exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    refine Eq.trans ?_ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _)
    rw [mul_comm, D.coc]

variable {D}

theorem exists_pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ D.Y), ∃ x h, z = cechPt D.f k x y h := by
  obtain ⟨x, y, h, hz⟩ := (hC D.Y X D.f k U).1 z
  exact ⟨y, x, h, hz⟩

def pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) : Fin (k + 1) → (U ⟶ D.Y) :=
  (exists_pts hC z).choose

theorem pts_spec (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ x h, z = cechPt D.f k x (pts hC z) h := by
  exact (exists_pts hC z).choose_spec

theorem pts_eq (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) (i j : Fin (k + 1)) :
    pts hC z i ≫ D.f = pts hC z j ≫ D.f := by
  obtain ⟨x, h, -⟩ := pts_spec hC z
  exact (h i).trans (h j).symm

theorem pts_cechPt (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ D.Y))
    (h : ∀ i, y i ≫ D.f = x) : pts hC (cechPt D.f k x y h) = y := by
  obtain ⟨x', h', hz⟩ := pts_spec hC (cechPt D.f k x y h)
  exact ((hC D.Y X D.f k U).2.1 _ _ _ _ _ _ hz).symm

theorem pts_res (hC : CechPt) {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech D.f) k U) (i : Fin (k + 1)) :
    pts hC (Sx.res g z) i = g ≫ pts hC z i := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.1 V g
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem pts_along (hC : CechPt) {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts hC (Sx.along z θ) i = pts hC z (θ.toOrderHom i) := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.2 p θ
  rw [← hz] at e
  rw [e, pts_cechPt]

theorem scalar_map {A B : CommRingCat.{0}} (f : A ⟶ B) (u : (A : Type)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map f.hom.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (D) in
theorem lineFun_res {U V : Scheme.{0}} {k : ℕ} (g : V ⟶ U) (y : Fin (k + 1) → (U ⟶ D.Y))
    (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) (y' : Fin (k + 1) → (V ⟶ D.Y))
    (hy' : ∀ i j, y' i ≫ D.f = y' j ≫ D.f) (e : ∀ i, y' i = g ≫ y i) :
    lineFun D y' hy' = (show Fin (k + 1) ⥤ (glCat 1).obj Γ(U, ⊤) from lineFun D y hy) ⋙
      ((glCat 1).map (Scheme.Γ.map g.op)).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j _ => ?_)
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y' i) (y' j) (hy' i j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.op).hom
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j)))
  rw [← scalar_map]
  congr 1
  rw [u_congr D (e i) (e j) (hy' i j) (by rw [Category.assoc, Category.assoc, hy i j]),
    D.nat g (y i) (y j) (hy i j)]
  rfl


variable (D) in
def lineMap (hC : CechPt) : cech D.f ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
      naturality := fun U U' g => by
        ext z
        exact lineFun_res D g.unop _ (pts_eq hC _) _ (pts_eq hC _) (fun i => pts_res hC g.unop _ i) }
  naturality n m θ := by
    ext U z
    change lineFun D (pts hC (Sx.along (show Sx (cech D.f) n.unop.len U.unop from z) θ.unop)) (pts_eq hC _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1))
      (u_congr D (pts_along hC _ θ.unop i) (pts_along hC _ θ.unop j) _ _)

theorem lineMap_exists : CrystallineSemistableComparison.E.CechPt → CrystallineSemistableComparison.E.LineMap := by
  intro hC X D
  refine ⟨lineMap D hC, ?_⟩
  unfold CrystallineSemistableComparison.E.LineData.IsMap
  intro V x a h
  have hp := pts_cechPt (D := D) hC x a h
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (D.u (pts hC (cechPt D.f 1 x a h) 0) (pts hC (cechPt D.f 1 x a h) 1) (pts_eq hC _ 0 1))) = _
  rw [u_congr D (congrFun hp 0) (congrFun hp 1) _ ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end GlobalTheory.CompanionTheory.CechLine
end
end

