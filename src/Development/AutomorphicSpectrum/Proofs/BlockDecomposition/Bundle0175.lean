module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0170
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobIdem
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FrobLc

variable {l : ℕ} [Fact l.Prime]

theorem frob_idem (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) : A.frob e = e := by
  change e ^ l = e
  have h := IsIdempotentElem.pow_succ_eq (l - 1) he
  rwa [Nat.sub_add_cancel (Fact.out : l.Prime).one_lt.le] at h

theorem lcRes_id (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) :
    lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (RingHom.id A.Ug))) f = f := by
  have e : Spec.map (CommRingCat.ofHom (RingHom.id A.Ug)) = 𝟙 (SU A) := by
    change Spec.map (𝟙 (CommRingCat.of A.Ug)) = 𝟙 _
    exact Spec.map_id _
  rw [e]
  ext x
  rfl

theorem phi_lcA (hN : LcNat) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU A) (ZMod (l ^ n))) : A.phi n (lcA A n f) = lcA A n f := by
  have h := (hN l H A hA n).1 A hA A.frob A.pdOk_frob (RingHom.id A.Ug)
    (fun e he => by rw [frob_idem A e he]; rfl) f
  rw [lcRes_id] at h
  exact h

section Gen
universe w w' u v u' v'
variable {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
  {σ : R →+* R'} {ρ : R' →+* R'}

theorem cls_congr {K : CrystallineSemistableComparison.Cx.{w} R} {k : ℕ} {x y : K.X k} (h : x = y) (hx : K.d k x = 0) (hy : K.d k y = 0) :
    K.cls x hx = K.cls y hy := by
  subst h; rfl

theorem pull_fix (m : Mor F F' σ) (p : Mor F' F' ρ) (j : ℕ) (h : ∀ z, p.pullC j (m.pullC j z) = m.pullC j z)
    (c : CH.H F j) : p.pull j (m.pull j c) = m.pull j c := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact cls_congr (h z) _ _
end Gen

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem phi_lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ)
    (z : Cn (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L j) :
    (phiMor M.P n).pullC j ((lcM hN H r M n).pullC j z) = (lcM hN H r M n).pullC j z := by
  funext s
  exact phi_lcA hN H _ (s.obj (Fin.last j)).1.property n _

theorem fPhi : CrystallineSemistableComparison.E.FPhi := fun hN l _ H r K M n j x =>
  pull_fix (lcM hN H r M n) (phiMor M.P n) j (phi_lcM hN H r M n j) ((pts H r M (𝟭 _) n).et 0 j x)

end GlobalTheory.CompanionTheory.FrobLc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeomPtGeomMap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FNatProof

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem geomPt_geomMap {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      geomPt N A ((pxMap (okToOC l K) u hu).app A y) := by
  refine gb_ext N ?_ ?_
  · have e1 : GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) ≫
        pullback.fst _ _ ≫ pullback.fst _ _ = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ u := by
      rw [GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst, Category.assoc]
    rw [Category.assoc, e1, geomPt_fst, ← Category.assoc, geomPt_fst, Category.assoc]
    rfl
  · rw [Category.assoc, GlobalTheory.Et.geomMap, pullback.lift_snd, geomPt_snd, geomPt_snd]

def lcPull (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) :
    Mor (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := elMap (pxMap (okToOC l K) u hu)
  τ _ := LinearMap.id
  nat _ _ := rfl

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem cls_surj {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (h : CH.H F n) :
    ∃ (z : Cn F n) (hz : d F n z = 0), (cx F).cls z hz = h := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact ⟨z, hz, rfl⟩

theorem pull_square {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
    {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
    {σ₁₂ : R₁ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₁₃ : R₁ →+* R₃} {σ₃₄ : R₃ →+* R₄}
    (a : Mor F₁ F₂ σ₁₂) (b : Mor F₂ F₄ σ₂₄) (c : Mor F₁ F₃ σ₁₃) (e : Mor F₃ F₄ σ₃₄) (j : ℕ)
    (h : ∀ z : Cn F₁ j, b.pullC j (a.pullC j z) = e.pullC j (c.pullC j z)) (x : CH.H F₁ j) :
    b.pull j (a.pull j x) = e.pull j (c.pull j x) := by
  obtain ⟨z, hz, rfl⟩ := cls_surj F₁ j x
  change (cx F₄).cls (b.pullC j (a.pullC j z)) _ = (cx F₄).cls (e.pullC j (c.pullC j z)) _
  simp only [h]

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ)
    (h : CH.H (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).L j) :
    (lcM hN H r M n).pull j ((lcPull H r u hu n).pull j h) =
      Model.pullMH u hu n j ((lcM hN H r N n).pull j h) :=
  pull_square (lcPull H r u hu n) (lcM hN H r M n) (lcM hN H r N n) (pullMor (pxMap (okToOC l K) u hu) n) j
    (fun z => funext fun s => rfl) h

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext v
  rfl

def gId (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).U c ⟶
      (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c) :=
  𝟙 (Spec (CommRingCat.of c.1.obj.Ug))

theorem gId_nat (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ)
    {c c' : El M.P} (φ : c ⟶ c') :
    gId H r u hu n c' ≫ ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).S.map ((lcPull H r u hu n).G.map φ)).unop =
      ((probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S.map φ).unop ≫ gId H r u hu n c :=
  (Category.id_comp _).trans (Category.comp_id _).symm

theorem gId_lc (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P)
    (f : LocallyConstant ((probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n).U ((lcPull H r u hu n).G.obj c)) (ZMod (l ^ n))) :
    (lcPull H r u hu n).τ c f = lcRes (l ^ n) (gId H r u hu n c) f :=
  (lcRes_id _ f).symm

theorem gId_pts (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (c : El M.P) :
    (pts H r M (𝟭 _) n).y c ≫ GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu) =
      gId H r u hu n c ≫ (pts H r N (𝟭 _) n).y ((lcPull H r u hu n).G.obj c) :=
  (geomPt_geomMap u hu c.1.obj c.2).trans (Category.id_comp _).symm

theorem key (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    (lcPull H r u hu n).pull j ((pts H r N (𝟭 _) n).et 0 j x) =
      (pts H r M (𝟭 _) n).et 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) :=
  hE hG (l ^ n) (El N.P) (El M.P) (probe H r (𝟭 (El N.P) ⋙ CategoryOfElements.π _) n)
    (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb N) (gb M) (pts H r N (𝟭 _) n) (pts H r M (𝟭 _) n)
    (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu)) (lcPull H r u hu n)
    (gId H r u hu n) (gId_nat H r u hu n) (gId_lc H r u hu n) (gId_pts H r u hu n) 0 (Or.inl rfl) j x

theorem nat_step (hE : CrystallineSemistableComparison.E.EtNat) (hG : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) {M N : Model l K} (u : M.X ⟶ N.X)
    (hu : u ≫ N.p = M.p) (n : ℕ) [NeZero (l ^ n)] (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb N)) j 0) :
    eM hN H r M n 0 j
        (pull _ (sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu))) _ j x) =
      Model.pullMH u hu n j (eM hN H r N n 0 j x) :=
  (congrArg ((lcM hN H r M n).pull j) (key hE hG H r u hu n j x).symm).trans (square hN H r u hu n j _)

theorem fNat : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FNat := by
  intro hE E hN l _ H r K M N u hu n j x
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact nat_step hE E.gen hN H r u hu n j x

end GlobalTheory.CompanionTheory.FNatProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemMulEqZero
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LcLogProof

variable {l : ℕ} [Fact l.Prime]

theorem eq_of_idem (A : PAlg l) {a b : A.W} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a.coeff 0 = b.coeff 0) : a = b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  set d := a - b with hd
  have hd3 : d * d * d = d := by
    rw [hd]
    linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'
  have hmem : d ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, hd, ← WittVector.constantCoeff_apply, map_sub, sub_eq_zero]
    exact h
  have hall : ∀ k : ℕ, d ∈ Ideal.span {(l : A.W)} ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← hd3, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ih) hmem
  have h0 : d = 0 := IsHausdorff.haus (A.completeW.toIsHausdorff) d fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hall k
  exact sub_eq_zero.1 h0

theorem teich_sum_one (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) : ∑ a, WittVector.teichmuller l (e a) = (1 : A.W) := by
  have ho : OrthogonalIdempotents fun i => (WittVector.teichmuller l (e i) : A.W) :=
    ⟨fun i => by
      show _ * _ = _
      rw [← map_mul, (he.idem i).eq],
     fun i j hij => by
      show _ * _ = _
      rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero]⟩
  refine eq_of_idem A ho.isIdempotentElem_sum IsIdempotentElem.one ?_
  show WittVector.constantCoeff (∑ a, (WittVector.teichmuller l (e a) : A.W)) = WittVector.constantCoeff (1 : A.W)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one]
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  exact he.complete

theorem mul_pow_congr {R : Type*} [CommRing R] {s x y : R} (h : s * x = s * y) (k : ℕ) :
    s * x ^ k = s * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    linear_combination y ^ k * h

theorem idem_mul_eq_zero {R : Type} [CommRing R] {c x : R} (hc : IsIdempotentElem c)
    (h : algebraMap R (Localization.Away c) x = 0) : c * x = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c) _ x).1 h
  cases k with
  | zero => simp only [pow_zero, one_mul] at hk; simp [hk]
  | succ k => simpa only [hc.pow_succ_eq] using hk

theorem toΓ_injective (B : Type) [CommRing B] : Function.Injective (toΓ B) := fun x y h => by
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  simpa [toΓ] using this

theorem pow_on_part (r : Roots l) (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) (x : A.Ug)
    (hp : IsPow (r.zeta A n) f (toΓ A.Ug x)) (a : ZMod (l ^ n)) (c : A.Ug) (hc : IsIdempotentElem c)
    (hf : ∀ p : PrimeSpectrum A.Ug, c ∉ p.asIdeal → f p = a) :
    c * (x - kb A (r.ρ n).1 ^ a.val) = 0 := by
  have hv : ∀ v : Spec (CommRingCat.of (Localization.Away c)),
      f ((Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) v) = a := by
    intro v
    refine hf (PrimeSpectrum.comap (algebraMap A.Ug (Localization.Away c)) v) fun hm => ?_
    have hu : IsUnit (algebraMap A.Ug (Localization.Away c) c) := IsLocalization.Away.algebraMap_isUnit c
    have hm' : algebraMap A.Ug (Localization.Away c) c ∈ PrimeSpectrum.asIdeal v := hm
    exact (PrimeSpectrum.isPrime v).ne_top (Ideal.eq_top_of_isUnit_mem _ hm' hu)
  have h := hp _ (Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) a hv
  have h2 : toΓ _ (algebraMap A.Ug (Localization.Away c) x) =
      toΓ _ (algebraMap A.Ug (Localization.Away c) (kb A (r.ρ n).1 ^ a.val)) := by
    rw [map_pow, map_pow, ← toΓ_nat, h, ← toΓ_nat]
    rfl
  refine idem_mul_eq_zero hc ?_
  rw [map_sub, toΓ_injective _ h2, sub_self]

theorem ug_injective (H : RIn l) (A : PAlg l) : Function.Injective (algebraMap A.U A.Ug) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 (H.tf A))

theorem kb_rho (r : Roots l) (A : PAlg l) (n : ℕ) :
    kb A (r.ρ n).1 = algebraMap A.U A.Ug (A.oC (rootSeqInt l n)) := by
  show A.cToUg (clToC l (r.ρ n).1) = _
  rw [r.hρ]
  exact A.cToUg_coe (rootSeqInt l n)

theorem root_pow (A : PAlg l) (n : ℕ) : A.oC (rootSeqInt l n) ^ l ^ n = 1 := by
  rw [← map_pow, show rootSeqInt l n ^ l ^ n = 1 from Subtype.ext (rootSeq_pow n), map_one]

theorem isLog_one (hEx : LogEx) (hMul : LogMul) (A : PAlg l) (n : ℕ) : IsLog A n 1 0 := by
  obtain ⟨y, hy⟩ := (hEx l A n).1 1 (map_one _)
  have h := hMul l A n 1 1 y y (map_one _) (map_one _) hy hy
  rw [mul_one] at h
  have h0 : y + y = y := (hEx l A n).2.1 _ _ _ h hy
  have : y = 0 := by linear_combination h0
  rwa [this] at hy

theorem isLog_pow (hEx : LogEx) (hMul : LogMul) (A : PAlg l) (n : ℕ) {w : A.W} {y : A.Acr n} (h1 : A.th w = 1)
    (hy : IsLog A n w y) (k : ℕ) : IsLog A n (w ^ k) ((k : A.Acr n) * y) := by
  induction k with
  | zero => simpa using isLog_one hEx hMul A n
  | succ k ih =>
    have h := hMul l A n (w ^ k) w _ _ (by rw [map_pow, h1, one_pow]) h1 ih hy
    rw [← pow_succ] at h
    have e : (k : A.Acr n) * y + y = ((k + 1 : ℕ) : A.Acr n) * y := by push_cast; ring
    rwa [e] at h

theorem natCast_q (A : PAlg l) (n : ℕ) : ((l ^ n : ℕ) : A.Acr n) = 0 := by
  rw [Nat.cast_pow]; exact A.pow_l_acr n

theorem log_on_part (hEx : LogEx) (hMul : LogMul) (hEps : LogEps) (A : PAlg l) (n : ℕ) {η u c : A.A} {v : ℕ}
    (hη : η ^ l ^ n = A.s (epsilon l)) (hz : A.sharp η ^ l ^ n = 1) (hc : IsIdempotentElem c)
    (hE : A.sharp c * (A.sharp u - A.sharp η ^ v) = 0) {y : A.Acr n}
    (h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1)
    (hy : IsLog A n (WittVector.teichmuller l (u ^ l ^ n)) y) :
    A.toAcr n (WittVector.teichmuller l c) * y = A.toAcr n (WittVector.teichmuller l c) * ((v : A.Acr n) *
      A.cris n (ACris.periodT (untilt_epsilon (p := l)))) := by
  have hq : 1 ≤ l ^ n := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  obtain ⟨m, hm⟩ : ∃ m, m + v = l ^ n * v := ⟨(l ^ n - 1) * v, by
    rw [Nat.sub_mul, one_mul]; exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hq)⟩
  set E : A.W := WittVector.teichmuller l c with hEdef
  set U : A.W := WittVector.teichmuller l u with hU
  set N : A.W := WittVector.teichmuller l η with hN
  have hEi : E * E = E := by rw [hEdef, ← map_mul, hc.eq]
  have hthE : A.th E = A.sharp c := rfl
  have hthU : A.th U = A.sharp u := rfl
  have hthN : A.th N = A.sharp η := rfl

  have hw1 : A.th (E * U * N ^ m + (1 - E)) = 1 := by
    have e1 : A.sharp η ^ (m + v) = 1 := by rw [hm, pow_mul, hz, one_pow]
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, hthE, hthU, hthN]
    rw [pow_add] at e1
    linear_combination A.sharp η ^ m * hE + A.sharp c * e1
  obtain ⟨yw, hyw⟩ := (hEx l A n).1 _ hw1
  have hwq := isLog_pow hEx hMul A n hw1 hyw (l ^ n)
  rw [natCast_q, zero_mul] at hwq

  have hε1 : A.th (WittVector.teichmuller l (A.s (epsilon l))) = 1 := by
    rw [← hη]; exact (map_pow A.sharp η (l ^ n)).trans hz
  have hεm := isLog_pow hEx hMul A n hε1 (hEps l A n) m
  have hprod := hMul l A n _ _ _ _ h1 (by rw [map_pow, hε1, one_pow]) hy hεm
  have hid : E * (E * U * N ^ m + (1 - E)) ^ l ^ n =
      E * (WittVector.teichmuller l (u ^ l ^ n) * WittVector.teichmuller l (A.s (epsilon l)) ^ m) := by
    have h2 : E * (E * U * N ^ m + (1 - E)) = E * (U * N ^ m) := by
      linear_combination (U * N ^ m - 1) * hEi
    rw [mul_pow_congr h2, ← hη, map_pow, map_pow, ← hU, ← hN, mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
  have key := (hEx l A n).2.2 E _ _ _ _ (show IsIdempotentElem E from hEi) hid hwq hprod
  have hm' : (m : A.Acr n) + (v : A.Acr n) = 0 := by
    have := congrArg (Nat.cast : ℕ → A.Acr n) hm
    rw [Nat.cast_add, Nat.cast_mul, natCast_q, zero_mul] at this
    exact this
  linear_combination (-1 : A.Acr n) * key + (A.toAcr n E * A.cris n (ACris.periodT (untilt_epsilon (p := l)))) * (-hm')

theorem lcLog : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul → CrystallineSemistableComparison.E.LogEps →
    CrystallineSemistableComparison.E.EpsRoot → CrystallineSemistableComparison.E.LcLog := by
  intro hI hS _ hEx hMul hEps hR l _ H r A hA n u f hp
  obtain ⟨η, hη, hsh⟩ := hR l n
  obtain ⟨e, he, hiff, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  have hz : A.sharp (A.s η) ^ l ^ n = 1 := by rw [hsh A]; exact root_pow A n
  have hη' : (A.s η) ^ l ^ n = A.s (epsilon l) := by rw [← map_pow, hη]
  have hid : ∀ a, IsIdempotentElem (A.sharp (e a)) := fun a => by
    show _ * _ = _
    rw [← map_mul, (he.idem a).eq]
  have hE : ∀ a : ZMod (l ^ n), A.sharp (e a) * (A.sharp u - A.sharp (A.s η) ^ a.val) = 0 := by
    intro a
    have hidg : IsIdempotentElem (algebraMap A.U A.Ug (A.sharp (e a))) := (hid a).map _
    have h := pow_on_part r A n f _ hp a _ hidg (fun p hpn => (hiff a p).1 hpn)
    rw [kb_rho] at h
    apply ug_injective H A
    rw [map_zero, ← h, hsh A]
    simp only [map_mul, map_sub, map_pow]
  have hsum : ∑ a, A.sharp (e a) = 1 := by
    have := congrArg A.th (teich_sum_one A he)
    rwa [map_sum, map_one] at this
  have h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1 := by
    have e0 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = A.sharp u ^ l ^ n := map_pow A.sharp u _
    rw [e0, ← one_mul (A.sharp u ^ l ^ n), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : A.sharp (e a) * A.sharp u = A.sharp (e a) * A.sharp (A.s η) ^ a.val := by
      linear_combination hE a
    rw [mul_pow_congr h2, ← pow_mul, mul_comm a.val, pow_mul, hz, one_pow, mul_one]
  obtain ⟨y, hy⟩ := (hEx l A n).1 _ h1
  have hloc := fun a : ZMod (l ^ n) => log_on_part hEx hMul hEps A n hη' hz (he.idem a) (hE a) h1 hy
  have hsumA : ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, teich_sum_one A he, map_one]
  have hlc := ((hS l H A hA n).2.2.2 f e he (fun a p hpn => (hiff a p).1 hpn))
  have hfin : y = (ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA A n f := by
    rw [Algebra.smul_def, hlc]
    show y = A.cris n _ * _
    rw [← one_mul y, ← hsumA, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hloc a]; ring
  rwa [← hfin]

end GlobalTheory.CompanionTheory.LcLogProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLogUnique
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.CrisLog

variable {l : ℕ} [Fact l.Prime]

theorem dpw_mul' {R : Type} [CommRing R] (k : ℕ) (c x : WittVector l R) :
    dpw k (c * x) = algebraMap _ (WL l R) c ^ k * dpw k x := by
  simp only [dpw, map_mul, mul_pow]; ring

theorem dpw_idem {R : Type} [CommRing R] (k : ℕ) {e x x' : WittVector l R} (he : IsIdempotentElem e)
    (h : e * x = e * x') :
    algebraMap _ (WL l R) e * dpw (k + 1) x = algebraMap _ (WL l R) e * dpw (k + 1) x' := by
  have key : e * x ^ (k + 1) = e * x' ^ (k + 1) := by
    have hp : e ^ (k + 1) = e := he.pow_succ_eq k
    calc e * x ^ (k + 1) = (e * x) ^ (k + 1) := by rw [mul_pow, hp]
      _ = (e * x') ^ (k + 1) := by rw [h]
      _ = e * x' ^ (k + 1) := by rw [mul_pow, hp]
  have key' := congrArg (algebraMap _ (WL l R)) key
  rw [map_mul, map_mul, map_pow, map_pow] at key'
  simp only [dpw]
  rw [mul_left_comm, key', mul_left_comm]

theorem dpw_mem (A : PAlg l) {x : A.W} (hx : A.th x = 0) (k : ℕ) : dpw k x ∈ A.Acr0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  rw [dpw_mul']
  exact mul_mem (pow_mem (Subalgebra.algebraMap_mem _ c) k) (A.dpw_xi_mem k)

theorem isLog_exists (A : PAlg l) (n : ℕ) (w : A.W) (hw : A.th w = 1) : ∃ y, IsLog A n w y := by
  have h0 : A.th (w - 1) = 0 := by rw [map_sub, hw, map_one, sub_self]
  exact ⟨_, fun k => ⟨dpw k (w - 1), dpw_mem A h0 k⟩, fun _ => rfl, rfl⟩

theorem isLog_unique (A : PAlg l) (n : ℕ) (w : A.W) (y y' : A.Acr n) (h : IsLog A n w y)
    (h' : IsLog A n w y') : y = y' := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  have e : g = g' := funext fun k => Subtype.ext ((hg k).trans (hg' k).symm)
  rw [e]

theorem isLog_local (A : PAlg l) (n : ℕ) (e w w' : A.W) (y y' : A.Acr n) (he : IsIdempotentElem e)
    (h : e * w = e * w') (hy : IsLog A n w y) (hy' : IsLog A n w' y') :
    A.toAcr n e * y = A.toAcr n e * y' := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have h1 : e * (w - 1) = e * (w' - 1) := by rw [mul_sub, mul_sub, h]
  have h2 : ∀ k, algebraMap A.W A.Acr0 e * g (k + 1) = algebraMap A.W A.Acr0 e * g' (k + 1) := fun k =>
    Subtype.ext (by
      change algebraMap A.W (WL l A.A) e * (g (k + 1)).1 = algebraMap A.W (WL l A.A) e * (g' (k + 1)).1
      rw [hg, hg']
      exact dpw_idem k he h1)
  have h3 : ∀ k, A.toAcr n e * A.mkAcr n (g (k + 1)) = A.toAcr n e * A.mkAcr n (g' (k + 1)) := fun k => by
    have := congrArg (A.mkAcr n) (h2 k)
    rwa [map_mul, map_mul] at this
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h3 k, mul_left_comm]

theorem logEx : CrystallineSemistableComparison.E.LogEx := fun l _ A n =>
  ⟨isLog_exists A n, fun w y y' => isLog_unique A n w y y', fun e w w' y y' => isLog_local A n e w w' y y'⟩

end GlobalTheory.CompanionTheory.CrisLog
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafPullConnectingCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheaf_pull_connecting_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hS' : S'.ShortExact) (α : S ⟶ S'.map (push f)) (n : ℕ) (x : Sheaf.H.{0} S.X₃ n),
    hPull f α.τ₁ (n + 1) (H.δ hS n (n + 1) rfl x) = H.δ hS' n (n + 1) rfl (hPull f α.τ₃ n x) := by
  first | exact @GlobalTheory.CompanionTheory.CechDelta.hPull_δ | exact GlobalTheory.CompanionTheory.CechDelta.hPull_δ | (intros; apply GlobalTheory.CompanionTheory.CechDelta.hPull_δ <;> assumption)
end

