Historical plan; for measured values see docs/DECISIONS.md and docs/M2_REPORT.md.

# CQRV — Claude Code ile yürütme planı

Bu plan, raporu (`cqrv_report_revised_v2.docx`) Claude Code ile adım adım yazılıma çevirmek için
hazırlandı. İş bölümü: **Claude Code** kodu yazar ve derler; **siz** matematiksel tasarım kararlarını
verir ve ispat yükümlülüklerini bölersiniz; **ben** her aşamanın çıktısını rapora karşı denetler,
sonraki görev metnini üretirim. Her aşama = bir Claude Code oturumu = bir PR.

## 0. Öneri listesinden aldıklarım ve ertelediklerim

| Öneri | Karar | Gerekçe |
|---|---|---|
| Tüm pipeline Lean 4'te (TCB küçük) | **Alındı** | Front end de Lean'de; yalnızca diferansiyel test koşumu Python |
| MVP = Faz I + II (Grover dilimi), `cqr certify` tek komut | **Alındı** | Aşama 9'un kabul kriteri |
| Sertifika şeması (JSON), SHA3-256, semver | **Alındı** | Aşama 8; raporun 9.5.3'üyle uyumlu |
| CLI komut yüzeyi `check/extract/match/synthesize/certify/emit` ve makine-okunabilir diagnostik | **Alındı** | Aşama 3–4'ten itibaren kademeli |
| Statevector simülatörüyle diferansiyel test (n ≤ 12) | **Alındı** | Aşama 5'in kabul kriteri; sentezleyici hatalarını ispattan önce yakalar |
| Regresyon korpusu (for / while / allocate_tree) | **Alındı** | Aşama 3–4 testleri |
| Kernel-check için referans donanım | **Alındı** | Aşama 8'de ölçüm betiği |
| İkinci predikat (RevLib/EPFL) | **Alındı** | Aşama 9'un kabul kriteri |
| LSP sunucusu / VS Code eklentisi | **Ertelendi** | M2'den sonra; diagnostik formatı şimdiden JSON tutulacak ki LSP'ye taşınması kolay olsun |
| Telemetri (match/near-miss oranları) | **Ertelendi** | Kütüphanede tek pattern varken anlamsız |
| Ek araç mühendisi + DevOps | **Kapsam dışı** | Claude Code bu rolün büyük kısmını alır; CI/paketleme Aşama 0 ve 8'de |
| MerLean autoformalization | **Ertelendi** | İspat iskeletleri için Aşama 7'de denenebilir, bağımlılık yapılmaz |

## 1. Çalışma protokolü

**Oturum başı (her aşama için):** `PLAN.md`'deki görev metnini Claude Code'a verin. Görev metni
aşama hedefini, dosyaları ve kabul kriterini içerir; `CLAUDE.md` kuralları zaten yüklüdür.

**Bana göndereceğiniz paket (her aşama sonunda):**
1. Claude Code'un kapanış özeti (CLAUDE.md "How to end every task" formatı)
2. `git diff --stat` ve değişen Lean dosyalarının tam içeriği (veya repo zip'i)
3. `lake build` son 40 satırı ve test çıktısı
4. `docs/SORRIES.md` ve `docs/DECISIONS.md`'nin güncel hali

**Benden alacağınız:** rapora karşı uygunluk denetimi (bölüm bölüm), hatalı/uydurma lemma
tespiti, ispat yükümlülüklerinin bölünmüş listesi, bir sonraki görev metninin güncellenmiş hali.

**Kapı kuralı:** Bir aşamanın kabul kriteri sağlanmadan sonrakine geçilmez; ama ispat
aşamaları (6–7) mühendislik aşamalarıyla (5, 8) paralel yürütülebilir — iki ayrı oturum.

**Oturum hijyeni:** Aşama başına yeni oturum. Bir oturumda 3'ten fazla derleme-düzeltme turu
sonuç vermiyorsa durun ve bana gönderin; "bir kez daha dene" döngüsü Lean'de nadiren işe yarar.

## 2. Aşamalar

Her aşamada: **Hedef · Rapor karşılığı · Claude Code görev metni · Teslimat · Kabul · Benim denetimim.**

---

### Aşama 0 — Repo, toolchain, CI (1 oturum)

**Hedef:** Derlenen boş iskelet; pinlenmiş toolchain; CI'da `lake build` + sorry denetimi.
**Rapor:** §9.1 (Faz I), §9.5.1, §9.5.3.

**Görev metni:**
> Create a Lean 4 project `cqrv` with the package layout in CLAUDE.md (empty modules with
> doc-comments naming their report sections). Pin `lean-toolchain` to the latest stable Lean 4
> release and add Mathlib as a dependency at a matching commit; record both in DECISIONS.md.
> Check whether `Lean-QuantumInfo` (Physlib) builds against that Mathlib commit; if yes add
> it, if not record the incompatibility in DECISIONS.md and leave it out (we will use an
> abstract channel interface until it does). Add `docs/SORRIES.md` (empty table) and a GitHub
> Actions workflow that runs `lake build`, then fails if any `sorry` appears outside the files
> listed in SORRIES.md, and prints `#print axioms` for every theorem in `CQRV/Certify`.
> Add `tests/diff/` with a `requirements.txt` (numpy) and a placeholder statevector simulator.
> Copy the two report documents into `docs/`. End with `lake build` green.

**Teslimat:** lakefile, manifest, CI yaml, boş modüller, docs/.
**Kabul:** `lake build` temiz; CI tanımı var; Physlib kararı DECISIONS.md'de.
**Benim denetimim:** Pinlenen sürümlerin makul olması; Physlib kararı; dizin → bölüm eşlemesi.

**Sizin kararınız (Aşama 0 öncesi):** Physlib uyumsuzsa Aşama 2'de soyut `Channel` arayüzüyle
başlamayı kabul ediyor musunuz? (Önerim: evet; raporun §9.1.1'i zaten bunu öngörüyor.)

---

### Aşama 1 — Kaynak dereceleri ve fibrasyon (1 oturum)

**Hedef:** `Grade`, `⊕`, `⊗`, sıralama, bütçe testi; monoid yasaları ispatlı.
**Rapor:** §3.1.1 (Tablo 3.1, revize ⊕: max/+/+/max), §3.1.2, §3.1.3 (profil = monoton harita).

**Görev metni:**
> In `CQRV/Grades`: define `structure Grade (w d t a : Nat)`; `seqComp` (⊕: max, +, +, max)
> and `parComp` (⊗: +, max, +, +) exactly as Table 3.1; `instance : CommMonoid Grade` for ⊕
> with identity (0,0,0,0) — prove the laws (`simp`, `omega`, `Nat.max_comm/assoc`); the
> component-wise partial order `≤` with `DecidableRel`; `fits (r b : Grade) : Bool := decide (r ≤ b)`;
> `structure HardwareProfile` as a monotone map Grade → Grade with a proof of monotonicity and
> `ρNISQ` from §3.3.3. Tests: the three-stage pipeline of §2.3.3 must give (12, 280, 900, 8);
> the Grover numbers of Table 3.3 must give (10, 74, 72, 2) from oracle (10,21,8,2) and
> diffusion (10,16,28,2) under ⊕ with r⋆ = 2. No sorry expected in this stage.

**Kabul:** Sıfır sorry; iki sayısal test `#guard` ile geçiyor.
**Benim denetimim:** ⊕ tanımının Tablo 3.1 ile birebir uyumu; `⊗`'nin yalnızca ayrık kayıtlar için
kullanıldığına dair doc-comment.

---

### Aşama 2 — Gerçekleştirilebilirlik tanımları ve Theorem 3.3a ifadesi (1–2 oturum)

**Hedef:** Definition 2.1–2.2, Theorem 3.3a'nın revize hipotezlerle ifadesi, ε = 0 hâli için ispat
denemesi; Theorem 3.3b ve Theorem 3.1 yalnızca ifade.
**Rapor:** §2.1, §2.2.2 (revize Theorem 3.1), §2.3.1–2.3.2 (R3/R4 ekleri).

**Görev metni:**
> In `CQRV/Realizability`: `Spec X Y := X → Y → Prop` with metric structure on `Y` as a
> typeclass; an abstract `Channel` interface (`structure Channel (n m : Nat)` with a density-
> operator semantics field if Physlib is available, otherwise an opaque type with `traceDist`
> and composition axioms recorded as a named trust boundary in DECISIONS.md); `encode`,
> `decode` (POVM as a finite family); `Realizes (f : Spec X Y) (Φ : Channel) (ε δ : ℝ) (r : Grade) : Prop`
> exactly as Definition 2.2. State `theorem measured_composition` (3.3a) with the explicit
> hypotheses: domain compatibility and non-expansiveness of the second stage, grades combined
> by ⊕. Prove the special case ε_f = ε_g = 0 if it closes within the session; otherwise leave a
> tracked sorry with the sub-lemma list. State `coherent_composition` (3.3b) with ideal/implemented
> channels and `η_f`, `η_g` as in §2.3.2, sorry. State `obstruction` (3.1) over `ClDet` with the
> non-degeneracy hypothesis, sorry. Do not attempt 3.3b or 3.1.

**Kabul:** Üç teorem derleniyor; 3.3a'nın ε = 0 hâli ya kapanmış ya SORRIES.md'de bölünmüş.
**Benim denetimim:** Hipotezlerin R3/R4/R6 ile birebir uyumu; `Channel` soyutlamasının Lemma 6.3.2'yi
ifade etmeye yetecek kadar güçlü olması (kısmi iz gerekli).

**Sizin kararınız:** `Y` üzerindeki metrik için Mathlib `MetricSpace` mi, yoksa yalnızca ayrık (ε = 0)
hâl mi? MVP için ayrık hâl yeter; genel hâli tip parametresi olarak açık bırakmayı öneririm.

---

### Aşama 3 — DSL ön ucu ve çıkarım ℰ (1–2 oturum)

**Hedef:** Parser, yüzey tipleme, Cl♭ yargısı, imza çıkarımı; regresyon korpusu.
**Rapor:** §7.1 (BNF, `for … with acc = … do` biriktirici), §7.2 (ℰ; sözdizimsel ĉ∧; `and_depth`),
§7.3 Tablo 3, §4.2.2 (iki katmanlı kabul: `while` elaborate edilir ve `iter = unbounded` ile çıkar;
`allocate_tree` Aşama 1'de reddedilir).

**Görev metni:**
> In `CQRV/DSL`: AST for the BNF of §7.1.4 (with the fold form of `for`); a parser (Lean
> `Parsec` or hand-written); surface type checker (Stage 1: rejects non-structural recursion and
> dynamic allocation with a JSON-serializable diagnostic); extractor `ℰ : TypedTerm → SigmaIn`
> following Table 3 of §7.3.2: `and` increments ĉ∧, `or` via De Morgan (one AND, no DNF),
> `for` as n-fold ⊕, `let` with live-range ancilla accounting, `while` allowed by the surface
> checker and extracted with `iter = unbounded`. `SigmaIn` must carry problem class, (n, ĉ∧,
> and_depth), ancilla budget, oracle structure with support set, algebraic structure, domain.
> Tests: `grover_pred_037` extracts to the signature of §7.2.3 (n = 8, ĉ∧ = 2, and_depth = 2,
> support {0,3,7}); the `while` example of §4.3.3 extracts with `iter = unbounded`;
> `allocate_tree(depth)` is rejected at Stage 1 with a diagnostic. CLI: `cqr check`, `cqr extract`.

**Kabul:** Üç korpus testi geçiyor; diagnostik JSON.
**Benim denetimim:** Tablo 3 kurallarının birebir uygulanması; `ĉ∧`'nin asla "minimum" diye adlandırılmaması.

---

### Aşama 4 — Eşleştirici, anti-unification, onarım ipucu (1–2 oturum)

**Hedef:** Normal form, Miller-örüntü eşleştirme (Algoritma 1, revize adımlar), Algoritma 2, lgg,
`dist`, borrow-checker tarzı mesaj.
**Rapor:** §4.1.1 (AC normalizasyonu), §4.1.2 (Adım 2 kapsam denetimi, Adım 4 tutarlılık),
§4.1.4 (`Bool_{F₁}`, aritmetik yan koşullar sonradan `decide`), §4.3.

**Görev metni:**
> In `CQRV/Matching`: pattern terms with metavariables; `normalize` (flatten AC combinators,
> sort arguments under a fixed symbol order); `millerMatch (φ : Pattern) (σ : SigmaIn) : Option Subst`
> implementing Algorithm 1 as revised: rigid decomposition, flexible-rigid assignment with the
> scope check, occurs check, consistency on repeated metavariables, arithmetic side conditions
> evaluated after substitution; `lgg` with metavariable reuse on identical disagreement pairs;
> `dist` = number of fresh metavariables, ties by substitution size; Algorithm 2 with early exit;
> `renderHint` producing the five-field diagnostic of Table 4 (§4.3.2) as JSON and as text.
> Library: a `Patterns` list with the Grover precondition φ_Grover of §4.1.4. Tests: Grover
> signature matches with σ(F₁)=8, σ(F₂)=32 and the side condition 32 ≥ 1 discharged; the
> `while` signature fails and yields the hint of §4.3.3 with `iter = F₃`; a term with a bound
> variable outside the metavariable's arguments fails the scope check. CLI: `cqr match`.

**Kabul:** Testler geçiyor; `match` çıktısı tekil (singleton) veya boş.
**Benim denetimim:** Normalizasyonun eşleştirmeden önce yapıldığı; birimlilik iddiasının kodda
korunduğu (backtracking yok).

---

### Aşama 5 — Devre IR'si ve oracle sentezleyici (1–2 oturum)

**Hedef:** Gate-level IR, TempLogicalAND (4-T), MBU, `Z(anc)` faz çevirme, Bennett zamanlaması,
derece hesabı; diferansiyel test.
**Rapor:** §6.1.2–6.1.4 (revize Tablo 2 ve 3), §6.2.2 (Gidney devresi), §6.3.1.

**Görev metni:**
> In `CQRV/Circuit`: a gate-level IR (H, S, T, T†, X, CNOT, CZ, Z, measure-X with classically
> controlled CZ, allocate/free ancilla) with `depth`, `tCount`, `width`, `peakAncilla` computed
> by a scheduler (sequential layers). In `CQRV/Synthesis`: `TempLogicalAND` exactly as the
> listing in §6.2.2 (4 T), `UncomputeTempLogicalAND` (0 T), `synthesizeOracle` for an AND
> chain with `Z` on the last ancilla (no phase qubit), a Bennett pebbling scheduler
> parameterized by `a_max`, and the grade of §6.3.1. In `tests/diff/`: a numpy statevector
> simulator that executes the IR (including mid-circuit measurement with both branches
> checked) and verifies, for n ≤ 12 and random predicates, that the synthesized oracle acts
> as `|x⟩ ↦ (−1)^{P(x)}|x⟩` on the data register and returns the ancillae to |0⟩ (state
> factorizes). Tests: the §6.1.4 oracle has grade (10, 21, 8, 2); Bennett table of §6.1.3 for
> c∧ = 8 gives executed T-count ≤ 32 × multiplier. CLI: `cqr synthesize`.

**Kabul:** Diferansiyel test rastgele 100 predikatta geçiyor; derece (10, 21, 8, 2).
**Benim denetimim:** Gidney devresinin kapı sırası (Fig. 3 ile karşılaştırma); MBU fix-up'ın her
iki ölçüm sonucunda doğru olması; derinlik sayımının Tablo 3 ile uyumu (21).

---

### Aşama 6 — Devre semantiği ve Lemma 6.3.2 (2–3 oturum; sizin ağırlığınız yüksek)

**Hedef:** IR'nin birimsel/yoğunluk-matrisi denotasyonu; TempLogicalAND doğruluğu; MBU kanal lemması;
Lemma 6.3.2 ifadesi ve ispat iskeleti.
**Rapor:** §9.1.1, §6.2.2 (kanal düzeyinde MBU doğruluğu), §6.2.4 (revize Layer 2–3), §6.3.2.

**Görev metni (oturum 6a):**
> In `CQRV/Circuit/Semantics`: denotation of the IR into `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`
> for the unitary fragment and into density-matrix channels (Physlib `CPTPMap` if available,
> otherwise the abstract `Channel` of Stage 2) for the measurement fragment. State and prove
> `tempLogicalAND_correct` on computational-basis inputs by explicit computation
> (`Fin 8` matrices; try `decide`/`norm_num` on exact entries over `ℚ(√2)`-free
> representation — if the 8×8 computation does not close, record the obligation). State
> `mbu_channel_correct`: compute; use; MBU-uncompute equals the ideal channel on the control
> register. State `Lemma_6_3_2` on density operators exactly as §6.3.2. Leave sorries tracked.

**Oturum 6b (ispat bölme):** Siz Lemma 6.3.2'yi alt-lemmalara bölersiniz (ölçüm dalı başına
kısmi iz hesabı, faz toplamı); her alt-lemma ayrı görev olur.

**Kabul:** Semantik derleniyor; `tempLogicalAND_correct` kapanmış ya da tam olarak hangi
hesaplamanın takıldığı belgelenmiş.
**Benim denetimim:** İfadelerin yoğunluk matrisi üzerinde olması (saf-durum değil); Theorem 3.3a'nın
iterasyon içinde çağrılmaması.

---

### Aşama 7 — Grover parametrik lemması (2–4 oturum; en ağır ispat)

**Hedef:** Figure 8.1 (lemma bağımlılık grafiği) sırasıyla: oracle reflection → diffusion
reflection → reflection geometry → iteration induction → terminal measurement → π.
**Rapor:** §8.2–8.3, §5.2.4 (revize Lean taslağı: `OracleCert`, `GroverParams`, `hM_card` hipotez).

**Görev metni (oturum 7a):**
> In `CQRV/Grover`: `OracleCert` and `GroverParams` as in §5.2.4 (revised); `GroverCircuit`
> built from the Stage 5 synthesizer and a diffusion operator; the statement of
> `grover_parametric_lemma` with `Realizes … (δ := 1 − sin²((2r⋆+1)θ))` and `AncRestore` on
> density operators. Then the lemma skeleton of Figure 8.1 as six named theorems with sorries
> and their dependency recorded in SORRIES.md. Prove `diffusion_reflection` (U_s = 2|s⟩⟨s| − I)
> first — it is pure linear algebra.

**Sonraki oturumlar:** her lemma ayrı; `reflection_geometry` ve `iteration_induction` SQIR'in
Coq ispatının yapısını izler (bana SQIR'in ilgili dosyasını gönderirseniz Lean'e çeviri taslağı
çıkarırım).

**Kabul (M2 için asgari):** `grover_parametric_lemma` kapanmış **ya da** kalan sorry'ler yalnızca
Lemma 6.3.2'ye bağlı ve bu açıkça SORRIES.md'de.
**Benim denetimim:** Her kapanan lemmanın ifadesinin rapordaki eşitliğe birebir karşılık gelmesi;
`#print axioms` çıktısında güven sınırı dışında aksiyom olmaması.

---

### Aşama 8 — Sertifika, denetim, emitter, CLI (1–2 oturum; Aşama 6–7 ile paralel)

**Hedef:** `Certificate` kaydı, JSON şeması, SHA3-256 hash'ler, `sorryAx`/aksiyom denetimi, QIR
metin emitter'ı (Adaptive Profile), referans donanımda kernel-check ölçümü.
**Rapor:** §5.2, §5.3, §8.4 (revize QIR listesi), §9.5.1 (sorry kuralı), §9.5.3.

**Görev metni:**
> In `CQRV/Certify`: `structure Certificate` with proof-term hash, grade, trust boundary,
> QIR profile, hardware-perturbation conjunct (δ_hw = δ + G·p̄ with G from the IR), predicate
> and circuit hashes (SHA3-256; implement or vendor a Lean SHA-3, record the decision);
> JSON serialization with a schema version; `auditAxioms` that fails on `sorryAx` or unlisted
> axioms. In `CQRV/Emit`: QIR text emitter following the §8.4.3 listing (opaque `%Qubit*`,
> `%Array*`, project-level callees lowered to `__quantum__qis__*`, Adaptive Profile header),
> plus OpenQASM 3. `scripts/bench_kernel.sh` measuring kernel-check time of the specialized
> certificate and printing CPU model, Lean and Mathlib commits. CLI: `cqr certify`, `cqr emit`.
> The CLI must print "certified" only when `auditAxioms` passes; otherwise "certificate with
> tracked obligations: …".

**Kabul:** `cqr certify grover_pred_037.cqr` → `certificate.json` + `.qir`; audit çıktısı dürüst.
**Benim denetimim:** JSON şemasının §8.4.2 alanlarını kapsaması; QIR profilinin Adaptive olması;
"verified" kelimesinin yalnızca sorry-free durumda basılması.

---

### Aşama 9 — M2 entegrasyonu ve ikinci predikat (1–2 oturum)

**Hedef:** Uçtan uca `cqr certify`; RevLib/EPFL'den XOR + `if` içeren ikinci predikat; durum
notlarının (Ch. 8 "target") gerçek ölçümlerle değiştirilmesi.
**Rapor:** §8.5, §9.2 Tablo 9.2 (ikinci predikat satırı), §8.5.3 kapsam notu.

**Görev metni:**
> Wire the full pipeline: `cqr certify` runs check → extract → match → instantiate →
> synthesize → certify → emit and writes a run report (stage, input, output, verification
> status) matching Table 8.5.2. Add a second predicate with an XOR chain and an `if` branch
> taken from RevLib/EPFL (record the source function), run the differential test, synthesize,
> and certify it with the same Grover QPLP (M computed symbolically if possible, otherwise
> supplied as a hypothesis as §5.1.3 prescribes). Produce `docs/M2_REPORT.md` with the measured
> grade, kernel-check time on the reference machine, the audit output, and the list of
> remaining tracked obligations.

**Kabul (= MVP):** İki predikat için sertifika + QIR; derece (10, 74, 72, 2) ölçülmüş; kalan
yükümlülükler listelenmiş.
**Benim denetimim:** M2_REPORT'un raporun Tablo 8.5.2 ve 8.4.4'ündeki "target" ifadelerini
hangi gerçek değerlerle değiştirebileceğimiz — raporun v3'ü bu aşamada yazılır.

---

## 3. Zaman çizelgesi (öneri; haftada 2–3 oturum varsayımıyla)

| Hafta | Aşamalar | Not |
|---|---|---|
| 1 | 0, 1 | Toolchain ve Physlib kararı en kritik gün-1 işi |
| 2–3 | 2, 3 | 2 ve 3 bağımsız; iki paralel oturum |
| 4–5 | 4, 5 | 5'in diferansiyel testi sentezleyiciyi ispattan önce güvenilir kılar |
| 6–9 | 6, 8 | 8 mühendislik, 6 ispat; paralel |
| 10–16 | 7 | Haftada bir lemma hedefi; takılan lemma bana gelir |
| 17–18 | 9 | M2 raporu; rapor v3 |

Raporun 12 aylık Faz I–II takvimine göre bu iddialı; Claude Code mühendislik aşamalarını
sıkıştırır, ispat aşamalarının (6–7) süresi ise esas olarak sizin ayıracağınız zamana bağlı.

## 4. Baştan verilmesi gereken üç karar

1. **Physlib yoksa soyut `Channel` ile başlamak** (Aşama 0/2) — önerim: evet.
2. **Metrik uzay genelliği** (Aşama 2) — önerim: tip parametresi olarak açık, MVP'de ayrık.
3. **Lean SHA-3 implementasyonu mu, Python yardımcı mı** (Aşama 8) — önerim: Lean (TCB ve
   "tek dil" ilkesi); kabul edilebilir alternatif: hash'i CLI dışından, ayrı denetlenebilir bir araçla.

## 5. Dosyalar

- `CLAUDE.md` — repo köküne.
- `docs/SORRIES.md` şablonu:

```
| File:line | Statement (short) | Report § | Depends on | Est. lines | Status |
|---|---|---|---|---|---|
```

- `docs/DECISIONS.md` şablonu:

```
## YYYY-MM-DD — <karar başlığı>
Decision: …
Why: …
Rejected: …
Report §: …
```
