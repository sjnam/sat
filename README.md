# Go를 위한 SAT 꾸러미

크누스가 『The Art of Computer Programming』 7.2.2.2절을 준비하며 쓴 SAT
풀이기들 가운데 가장 빠른
[**SAT13**](https://www-cs-faculty.stanford.edu/~knuth/programs/sat13.w)
(알고리즘 7.2.2.2C, CDCL)을 Go 꾸러미로 옮겼다.

크누스의 프로그램은 표준 입력으로 절을 받는 명령이다. 이 꾸러미는 같은 알맹이를
다른 Go 프로그램이 절을 넘기고 답을 받을 수 있는 라이브러리로 만든다. 옮기는
원칙은 하나다. **같은 입력과 같은 매개변수에서 mem 수가 C 원본과 똑같이 나와야
한다.**

## 진행

| 단계 | 글 | 내용 | 상태 |
| --- | --- | --- | --- |
| 1 | `sat.w` | 리터럴, 풀이기의 겉모습, 절 쌓기 | 완료 |
| 1 | `io.w` | 크누스 형식과 DIMACS 형식 읽기 | 완료 |
| 2 | `cdcl.w` | SAT13의 알맹이: 강제, 활동도, 충돌 학습, 절 재활용 | 완료 |
| 3 | `simplify.w` | SAT12 전처리와 SAT12-ERP 되살림 | 완료 |
| 4 | `cdcl.w` | 가정 리터럴, 풀이 사이에 상태를 간직하는 점진적 풀이 | 완료 |

SAT12 전처리도 벤치마크 113개 전부에서 C 원본과 mem, 줄인 절, erp 파일이 모두 같다.
`testdata`의 문제 여덟은 매개변수 여덟 가지로 전처리한 뒤 SAT13으로 풀고 해를
되살리기까지 원본 파이프라인(`sat12 | sat13 | sat12-erp`)과 견준다.

크누스의 벤치마크 113개 전부를 mem 10⁸에서 끊어 C 원본과 견주었고, 준비 mem과
풀이 mem이 모두 한 개도 틀리지 않는다. `testdata`의 작은 문제 여섯은 매개변수를
바꿔 가며 끝까지 풀어 견준다.

가정 리터럴과 점진적 풀이는 원본에 없으니 견줄 mem도 없다. 대신 답이 옳은지를 본다.
무작위 식에 절을 조금씩 보태며 가정을 주어 풀고 모든 배정을 따지는 방법과 견주고,
벤치마크를 넷으로 나눠 쌓아 가며 푼 답을 새 풀이기의 답과 견준다. 가정 없이 처음 푸는
풀이는 여전히 원본과 mem 하나 다르지 않다.

## 맛보기

```go
s := sat.New()
x, y := s.NewVar(), s.Lookup("y") // 이름 없는 변수와 이름 있는 변수
s.AddClause(x, y.Not())
s.AddClause(y)

st, err := s.Solve(context.Background()) // sat.Sat, sat.Unsat, sat.Unknown
if st == sat.Sat {
    fmt.Println(s.Value(x), s.Model()) // 리터럴 하나의 값, 트레일 차례의 해
}
fmt.Println(s.Stats()) // 크누스의 작별 인사와 같은 꼴
```

같은 풀이기에 절을 더 보태고 다시 풀면 처음부터 새로 짓지 않는다. 배운 절, 활동도,
옛 값, 수준 0에서 참이 된 리터럴을 간직한 채 이어 푼다. 가정 리터럴을 주면 그 가정
아래에서 풀고, 만족할 수 없으면 `Failed`가 책임이 있는 가정들을 알려 준다.

```go
st, err = s.Solve(ctx, x, y)   // x와 y를 가정하고 푼다
if st == sat.Unsat {
    fmt.Println(s.Failed())    // 책임이 있는 가정들, 비었으면 가정과 상관없이 UNSAT
}
s.AddClause(x.Not(), y.Not()) // 절을 더 보태고
st, err = s.Solve(ctx)         // 배운 것을 이어 쓰며 다시 푼다
```

`Timeout`과 `Doomsday` 말고 다른 매개변수를 바꾸면 간직한 상태를 버리고 처음부터 짓는다.

크누스의 SAT12 전처리를 먼저 돌릴 수도 있다. 전처리가 없앤 변수의 값은 풀이 뒤에
erp 자료로 되살아나므로 `Value`와 `Model`은 여전히 원래 변수들로 답한다.

```go
st, err := s.Simplify(ctx) // Unsat: 전처리만으로 증명, Sat: 절이 모두 사라짐, Unknown: 남은 절이 있음
st, err = s.Solve(ctx)     // 줄인 절을 풀고 해를 되살린다
fmt.Println(s.SimplifyStats())
s.WriteSimplified(w)       // 원본 sat12가 찍는 꼴의 줄인 절
s.WriteERP(w)              // 원본 sat12가 쓰는 erp 파일의 꼴
```

파일에서 읽을 수도 있다.

```go
f, _ := os.Open("foo.cnf")
err := s.ReadDIMACS(f) // 또는 s.ReadKnuth(f)
```

매개변수는 크누스의 명령 줄 선택과 같다. `s.Params.Set("s3")`처럼 원본의 선택
글자로 줄 수도 있고, `s.Params.Timeout = 1e9`처럼 필드에 직접 넣을 수도 있다.
mem 한도에 이르면 `sat.ErrTimeout`, `context`를 거두면 `ctx.Err()`와 함께
`sat.Unknown`을 돌려준다.

리터럴은 크누스를 따라 변수 k에 대해 `2k`(양)와 `2k+1`(음)이다.
변수 번호는 이름이 처음 나온 차례로 매겨진다. DIMACS 변수 k의 이름은 `"k"`다.

## 예제

```sh
go run ./examples/waerden -j 3 -k 3     # 반 데르 바르덴 수 W(3,3)
go run ./examples/queens -n 8 -count    # n-퀸의 해 세기
go run ./examples/sudoku                # 인칼라의 스도쿠, 해가 하나뿐임의 증명
go run ./examples/life                  # 생명 게임을 거꾸로 돌리기
go run ./examples/factor -n 4294967297  # 곱셈기를 거꾸로 돌려 인수분해하기
go run ./examples/hamsat -m 6 -n 6      # 컷셋 절을 보태 가며 닫힌 나이트 여행 찾기
```

- **waerden** — 크누스가 7.2.2.2절을 여는 문제. 1..n을 두 빛깔로 칠하되 한 빛깔로
  칠한 길이 j인 등차수열도, 다른 빛깔로 칠한 길이 k인 등차수열도 없게 할 수 있을까?
  n을 늘려 가며 풀다가 처음 UNSAT이 되는 곳이 반 데르 바르덴 수다. W(3,3)=9,
  W(3,4)=18, W(3,5)=22, W(4,4)=35를 모두 0.1초 안팎에 확인한다.
- **queens** — BDD 꾸러미의 같은 이름 예제와 짝. SAT는 100-퀸의 해 하나를 0.2초에
  찾지만, 해를 세려면 막는 절을 더해 가며 하나씩 찾아야 한다. 풀이 사이에 배운 것을
  간직하므로 8-퀸의 92개는 0.01초, 10-퀸의 724개는 0.25초에 센다(부를 때마다 새로
  짓던 때는 23초). 그래도 해의 수만큼 풀어야 하니 해를 한꺼번에 세는 BDD와는 길이 다르다.
- **sudoku** — 변수 729개, 절 12,009개. 인칼라의 ``세상에서 가장 어려운 스도쿠''를
  mem 36만 개에 풀고, 찾은 해를 막는 절을 더해 다시 풀어서 해가 하나뿐임을 증명한다.
- **life** — 주어진 무늬의 k세대 전 조상을 찾는다. 이웃 아홉 칸의 배정 512가지를 절로
  적는 가장 곧은 인코딩을 쓰고, 찾은 조상은 앞으로 돌려 확인한다. 조상이 없으면
  에덴의 동산이다. 기본 무늬는 `SAT`라는 글자.
- **factor** — 곱셈기 회로를 Tseitin 변환으로 절로 적고 곱을 N으로 못 박는다.
  오일러가 쪼갠 페르마 수 F5 = 641 × 6700417을 3초 남짓에 찾고, 2147483647이
  소수라는 것은 UNSAT으로 2.6초에 증명한다.
- **hamsat** — 크누스가 2026년 4월에 쓴 HAMSAT(알고리즘 7.2.2.4C)의 앞과 뒤를 옮겼다.
  꼭짓점마다 나가고 들어오는 호가 하나씩이라는 절로 순환 덮개를 찾고, 순환이 여럿이면
  합쳐 보다가 컷셋 절을 보태 다시 푼다. 원본이 SAT13을 품고 하던 일은 이 꾸러미의
  점진적 풀이가 맡는다. SGB 그래프 파일 스물넷에서 원본과 답이 모두 같았다. Petersen
  그래프는 7라운드, GP(23,2)는 258라운드 만에 해밀턴 순환이 없음을 보인다.

## 만들기

`.w`를 손보려면 [GWEB](https://github.com/sjnam/gweb)이 필요하다.

```sh
make          # .w를 Go로 짜내고 빌드한다
make test     # 시험을 돌린다
make pdf      # 문학적 문서를 조판한다
make check    # 조판 로그에 경고가 하나도 없는지 확인한다
```

크누스의 벤치마크 전부로 시험하려면
[SATexamples.tgz](https://www-cs-faculty.stanford.edu/~knuth/programs/SATexamples.tgz)를
풀어 두고 `SATEXAMPLES=<그 디렉터리> go test ./...`처럼 돌린다.

## 파일

- `knuth/`: 크누스의 원본 CWEB 프로그램 (sat0w, sat8, sat11, sat11k, sat12,
  sat12-erp, sat13, dimacs-to-sat, sat-to-dimacs)
- `testdata/`: SATexamples에서 고른 작은 문제 여섯, 두 형식으로 하나씩
