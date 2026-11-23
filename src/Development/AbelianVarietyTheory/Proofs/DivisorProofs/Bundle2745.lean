module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasY
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_measY (t : T) (j : ℕ) : ∃ (μ : Measure (GA D (Yc D j))) (𝓕 : Set (GA D (Yc D j))),
    (j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) ∧
    (j = D.R.m - 1 → IsMeasDef (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) := by
  have hLev := GlobalTheory.Mem.LevelOK.levOK_all D
  by_cases hj : j = D.R.m - 1
  · subst hj
    obtain ⟨μ, 𝓕, hμ⟩ := measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D)
      (Yc D (D.R.m - 1)) _ (D.sp.Y_sig _) (GlobalTheory.Mem.EasyInputs.spOK D).1
      (hLev _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)).1
    exact ⟨μ, 𝓕, fun h2 => absurd h2 (by omega), fun _ => hμ⟩
  · obtain ⟨μ, 𝓕, hμ⟩ := Formalism.IndefR.Eqv.measFDExists_holds D (Yc D j) (D.sp.Y_sig _) _ (hLev _ (R.βY j) (R.datYt t j R.triv)).1
    exact ⟨μ, 𝓕, fun _ => hμ, fun h' => absurd h' hj⟩

theorem exists_measX (t : T) : ∃ μ 𝓕, IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) D.sp.X' _ D.sp.X'_sig
    (GlobalTheory.Mem.EasyInputs.spOK D).2 (GlobalTheory.Mem.LevelOK.levOK_all D _ R.βX (R.datXt t)).1

theorem exists_measV (hv : ∀ i, (Vc D i).IsPosDef) (i : Fin D.R.m) (t : T) :
    ∃ μ 𝓕, IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) (Vc D i) _ (D.sp.V_sig _)
    (fun τ => Or.inl (hv i τ)) (GlobalTheory.Mem.LevelOK.levOK_all D _ (R.βV i) (R.datVt i t)).1


set_option maxHeartbeats 1000000 in
theorem exists_modX (t : T) : ∃ (H : HMod (Bridge.Gf D.sp.X' → R.cX.W)) (j : A.fam.amb.FR t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ)
      (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) ∧ ∀ x, H.e (j x) = R.B.jR t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ) (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := R.cX.W) (R.B.R t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.R t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jR t) (fun x => by exact (R.B.R t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)


set_option maxHeartbeats 1000000 in
theorem exists_modV (i : Fin D.R.m) (t : T) :
    ∃ (H : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (j : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
        (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) ∧
    ∀ x, H.e (j x) = R.B.jL i t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := (R.cV i).W) (R.B.L i t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.L i t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jL i t) (fun x => by exact (R.B.L i t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)

variable {R}

open Classical in
theorem idem_of_is {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) :
    Disjoint L.Pg (L.Q t) ∧ ∃ e : AE D, IsIdemSum e (L.Pg ∪ L.Q t) :=
  ⟨(GlobalTheory.ChainEquiv.places_sep L μ0 hL t).2, GlobalTheory.CentralShift.exists_idemSum _ fun _ hP _ hP' =>
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')⟩

theorem sd_of_frame {V : HSp D} {β Λ N} (h : IsSDFrame V β Λ N) : IsSelfDualC V Λ ∧ IsFrame β Λ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc, hc.1⟩

theorem exists_kerY (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T) (k : ℕ)
    (hv : k + 1 < D.R.m → IsVacO R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k)) :
    ∃ ω v, k + 1 < D.R.m → IsWeilDatumO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1))
        (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) v := by
  by_cases hk : k + 1 < D.R.m
  · have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).1 k hk
    obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D k) (Yc D (k + 1)) _ _
      (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    have s1 := sd_of_frame (hL.βY k (by omega))
    have s2 := sd_of_frame (hL.βY (k + 1) hk)
    obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
      (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vac k) (hv hk)
    exact ⟨ω, v, fun _ => ⟨hω, hv'⟩⟩
  · exact ⟨1, 0, fun h => absurd h hk⟩

theorem exists_kerX (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T)
    (hv : IsVacO R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX) :
    ∃ ω v, IsWeilDatumO R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX
        (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) R.vacX v := by
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.1
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D (D.R.m - 1)) D.sp.X' _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βY _ hm)
  have s2 := sd_of_frame hL.βX
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX)
    (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
    (idem_of_is hL t).1 (idem_of_is hL t).2 R.vacX hv
  exact ⟨ω, v, hω, hv'⟩

theorem exists_kerP (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (i : Fin D.R.m) (t : T)
    (hv : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i)) :
    ∃ ω v, IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 ω ∧
      IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
        R.Pg (R.Q t) (R.xiR t) (R.vacP i) v := by
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.2 i
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Vc D i) (Wc D i) _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βV i)
  have s2 := sd_of_frame (hL.βW i)
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
    (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2 (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vacP i) hv
  exact ⟨ω, v, hω, hv'⟩

end GlobalTheory.TupExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicIntCharpolyCommuteFrobeniusSemilinear
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem mem_range_zmod_of_pow_eq_self (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (c : k) (hc : c ^ p = c) : c ∈ Set.range ((ZMod.castHom (dvd_refl p) k)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card p] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := Polynomial.natDegree_X_pow_sub_X hp
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    ((ZMod.castHom (dvd_refl p) k)).injective hcard
  have hmem : c ∈ ((X ^ p - X : (ZMod p)[X]).map ((ZMod.castHom (dvd_refl p) k))).roots := by
    rw [Polynomial.mem_roots]
    · simp [hc]
    · simpa using (Polynomial.X_pow_sub_X_ne_zero hp : (X ^ p - X : k[X]) ≠ 0)
  rw [← hmap, hroots, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_map_eq_of_frobenius_eq (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (x : WittVector p k) (hx : WittVector.frobenius x = x) :
    ∃ y : WittVector p (ZMod p), WittVector.map ((ZMod.castHom (dvd_refl p) k)) y = x := by
  have hc : ∀ n, ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = x.coeff n := by
    intro n
    have h := congrArg (fun z => z.coeff n) hx
    simp only [WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def] at h
    exact mem_range_zmod_of_pow_eq_self p _ h
  choose a ha using hc
  refine ⟨WittVector.mk p a, ?_⟩
  ext n
  simp [WittVector.map_coeff, ha]

theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [PerfectRing k p] (f g : ℤ_[p] →+* WittVector p k) : f = g := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  have hI : Ideal.span {(p : WittVector p k)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact (WittVector.irreducible p).not_isUnit
  have h := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro m
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m x)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f y - g y, ?_⟩
  have h1 : x = ((x.appr m : ℕ) : ℤ_[p]) + y * (p : ℤ_[p]) ^ m := by rw [hy]; ring
  rw [h1]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem charpoly_map_eq_of_commute_semilinear {R : Type} [CommRing R] [IsDomain R]
    (σ : R →+* R) (hσ : Function.Surjective σ) (N : Type) [AddCommGroup N] [Module R N]
    [Module.Free R N] [Module.Finite R N] (F : N →ₛₗ[σ] N) (u : N →ₗ[R] N)
    (hF : Function.Injective F) (hu : ∀ x, u (F x) = F (u x)) :
    u.charpoly.map σ = u.charpoly := by
  classical
  let b := Module.Free.chooseBasis R N
  let U := LinearMap.toMatrix b b u
  let Φ : Matrix _ _ R := fun i j => b.repr (F (b j)) i
  have hFrepr : ∀ x i, b.repr (F x) i = ∑ j, Φ i j * σ (b.repr x j) := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, Finset.sum_apply',
      map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hurepr : ∀ y i, b.repr (u y) i = ∑ l, U i l * b.repr y l := by
    intro y i
    rw [← LinearMap.toMatrix_mulVec_repr b b u y]
    rfl
  have hcomm : U * Φ = Φ * U.map σ := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg (fun z => b.repr z i) (hu (b j))
    rw [hurepr, hFrepr] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [Matrix.map_apply, show U l j = b.repr (u (b j)) l from LinearMap.toMatrix_apply b b u l j]
  have hdet : Φ.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    choose w hw using fun j => hσ (v j)
    let x := b.repr.symm (Finsupp.equivFunOnFinite.symm w)
    have hx : ∀ j, b.repr x j = w j := by simp [x]
    have hFx : F x = 0 := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [hFrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hx, hw]
    have hx0 : x = 0 := hF (by rw [hFx, map_zero])
    apply hv0
    funext j
    rw [← hw j, Pi.zero_apply, ← hx j, hx0, map_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]
  rw [← LinearMap.charpoly_toMatrix u b, ← Matrix.charpoly_map]
  have hm : U.charmatrix * (Polynomial.C : R →+* _).mapMatrix Φ =
      (Polynomial.C : R →+* _).mapMatrix Φ * (U.map σ).charmatrix := by
    rw [Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub, ← map_mul, hcomm, map_mul,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hd
  have hC : Polynomial.C Φ.det ≠ 0 := Polynomial.C_ne_zero.2 hdet
  rw [mul_comm] at hd
  exact (mul_left_cancel₀ hC hd).symm

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem exists_monic_map_eq_charpoly : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N),
    Function.Injective F → (∀ x, u (F x) = F (u x)) →
      ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  intro p _ k _ _ _ N _ _ _ _ F ψ u hF hu
  have hfix := charpoly_map_eq_of_commute_semilinear _
    (WittVector.frobenius_bijective p k).surjective N F u hF hu
  have hψ : ψ = (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom := padicInt_ringHom_ext p _ _
  have hl : u.charpoly ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h : WittVector.frobenius (u.charpoly.coeff n) = u.charpoly.coeff n := by
      conv_rhs => rw [← hfix]
      rw [Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := exists_map_eq_of_frobenius_eq p _ h
    refine ⟨WittVector.equiv p y, ?_⟩
    rw [hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, hy]
  obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic u)
  exact ⟨P, hPm, hP⟩

end GlobalTheory.DieuCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelSupFrobeniusKernel
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.FrobKerInter

theorem isHopfIdeal_sup {k A : Type} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k] : (I ⊔ J).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 := Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hy
    have h2 := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars k) hz
    rw [map_add (f := _), h1, h2, add_zero]
  · intro x hx
    set K := (I ⊔ J).restrictScalars k
    have key : ∀ (L : Ideal A) [L.IsHopfIdeal k], L ≤ I ⊔ J → ∀ y ∈ L,
        TensorProduct.map K.mkQ K.mkQ (comul (R := k) y) = 0 := by
      intro L _ hL y hy
      have hle : L.restrictScalars k ≤ K := fun a ha => hL ha
      have e : K.mkQ = (Submodule.mapQ (L.restrictScalars k) K LinearMap.id hle) ∘ₗ
          (L.restrictScalars k).mkQ := by
        rw [Submodule.mapQ_mkQ, LinearMap.comp_id]
      rw [e, TensorProduct.map_comp, LinearMap.comp_apply,
        Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := L.restrictScalars k) hy, map_zero]
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), key I le_sup_left y hy, key J le_sup_right z hz, add_zero]
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Ideal.IsHopfIdeal.antipode_mem (R := k) hy)
      (Ideal.IsHopfIdeal.antipode_mem (R := k) hz)

theorem exists_quotient_kerIdeal_sup_frobKerIdeal : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  intro p hp k _ _ G H q
  have : (kerIdeal (q.app 1)).IsHopfIdeal k := isHopfIdeal_kerIdeal_of_bialgHom k _ _ (q.app 1)
  have : (frobKerIdeal p k (G.A 1)).IsHopfIdeal k := by
    let J := frobKerIdeal p k (G.A 1)
    let f := Ideal.Quotient.mkₐ k J
    refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
    · exact frobKerIdeal_le_augIdeal hp.out.ne_zero k (G.A 1)
    · intro x hx
      have h : J ≤ RingHom.ker
          ((Algebra.TensorProduct.map f f).comp (comulAlgHom k (G.A 1))) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply,
          FrobKerOrder.map_pow_eq, comulAlgHom_apply, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul, ← map_pow]
        have hpow : f (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [hpow, tmul_zero]
      exact h hx
    · intro x hx
      have h : J ≤ J.comap (HopfAlgebra.antipodeAlgHom k (G.A 1)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := k) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx
  set I := kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) with hI
  have : I.IsHopfIdeal k := isHopfIdeal_sup _ _
  let π : G.A 1 →ₐc[k] G.A 1 ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : Module.Finite k (G.A 1) := G.finite 1
  refine ⟨G.A 1 ⧸ I, inferInstance, inferInstance, KerGrp.isCocomm_of_surjective π hπ,
    Module.Finite.of_surjective (π : G.A 1 →ₗ[k] G.A 1 ⧸ I) hπ, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_, FrobKerOrder.le_sq p k (G.A 1)⟩
  intro a ha
  obtain ⟨b, rfl⟩ := hπ a
  have hb : b ∈ augIdeal k (G.A 1) := ha
  change Ideal.Quotient.mk I b ^ p = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (pow_mem_frobKerIdeal hb)

end GlobalTheory.PDiv.FrobKerInter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientOfGaloisStableFiniteSubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.Quot

theorem over_ext_of_pt_eq {K : Type} [Field K] {H Z : Over (Sp K)} [IsReduced H.left]
    [LocallyOfFiniteType H.hom] [IsSeparated Z.hom] (a b : H ⟶ Z)
    (h : ∀ y : ptOver K (AlgebraicClosure K) ⟶ H, y ≫ a = y ≫ b) : a = b := by
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback H.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd H.hom q)
  have hd : Dense (closedPoints ↥(pullback H.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst H.hom q).surjective.denseRange.dense_image
    (pullback.fst H.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι a.left b.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback H.hom q)) := hw₀
    let y : Sp Ω ⟶ H.left :=
      pointOfClosedPoint (pullback.snd H.hom q) w hw ≫ pullback.fst H.hom q
    have hy : y ≫ H.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : ptOver K Ω ⟶ H := Over.homMk y hy
    have hx : y ≫ a.left = y ≫ b.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι a.left b.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst H.hom q) (pointOfClosedPoint_apply (pullback.snd H.hom q) w hw _)
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom
    ((Over.w a).trans (Over.w b).symm) (equalizer.ι _ _) (equalizer.condition _ _))

end GlobalTheory.AV.Quot

namespace GlobalTheory.AV.AbVar

theorem exists_quot_of_galois_stable : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G →
    ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) →
    ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ deg q = Nat.card G ∧ (ptMap q).ker = G ∧
      ∀ (C : AbVar K) (f : A ⟶ C), G ≤ (ptMap f).ker → ∃ g : B ⟶ C, q ≫ g = f := by
  intro K _ A G hfin hn hgal
  obtain ⟨H, _, i, hi, hmono, hfinH, het, hG⟩ := GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points K A G hfin hn hgal
  obtain ⟨B, q, hq, hker⟩ := GlobalTheory.T.exists_quotient_abelianVariety_by_finiteSubgroup K A H i hi hmono hfinH
  have : IsReduced H.left := GlobalTheory.isReduced_of_smooth_of_isReduced H.hom

  have hext : ∀ (Z : Over (Sp K)) [IsSeparated Z.hom] (a b : H ⟶ Z),
      (∀ y : A.Pt, y ∈ G → ∀ (y' : ptOver K (AlgebraicClosure K) ⟶ H), y' ≫ i = y → y' ≫ a = y' ≫ b) →
      a = b := by
    intro Z _ a b hab
    exact GlobalTheory.AV.Quot.over_ext_of_pt_eq a b fun y' => hab _ ((hG _).2 ⟨y', rfl⟩) y' rfl
  have hkerG : (ptMap q).ker = G := by
    ext x
    rw [MonoidHom.mem_ker, ptMap_apply, hker, hG]
  refine ⟨B, q, hq, ?_, hkerG, ?_⟩
  · rw [GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed K A B q (Nat.card G) hn hq, hkerG]
    intro T x hx
    obtain ⟨y, rfl⟩ := (hker T x).1 hx
    have := A.ab.proper
    have hpow : i ^ Nat.card G = 1 := by
      refine hext A.X _ _ ?_
      intro z hz y' hy'
      rw [MonObj.comp_pow, hy', MonObj.comp_one]
      have h1 := pow_card_eq_one' (G := G) (x := ⟨z, hz⟩)
      exact congrArg Subtype.val h1
    rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
  · intro C f hf
    refine GlobalTheory.AV.AbVar.exists_factor_of_isogeny K A B C q f hq ?_
    intro T x hx
    obtain ⟨y, rfl⟩ := (hker T x).1 hx
    have := C.ab.proper
    have hif : i ≫ f.hom = 1 := by
      refine hext C.X _ _ ?_
      intro z hz y' hy'
      rw [← Category.assoc, hy', MonObj.comp_one]
      exact hf hz
    rw [Category.assoc, hif, MonObj.comp_one]

end GlobalTheory.AV.AbVar
end

