# SAT 꾸러미는 문학적 프로그램이다. .w 파일만이 원본이고 .go와 .pdf는
# 모두 생성물이다. `make`는 .w를 Go로 짜내어 빌드하고, `make pdf`는 조판한다.
#
# 다만 라이브러리 API의 .go는 저장소에 넣어 두고 clean에서도 빼 둔다.
# `go get`으로 이 꾸러미를 가져다 쓰는 쪽에 GWEB을 깔라고 할 수는 없다.
#
#   sat.w   리터럴, 풀이기의 겉모습, 절 쌓기
#   io.w    크누스 형식과 DIMACS 형식 읽기
#   cdcl.w  SAT13의 알맹이 (알고리즘 7.2.2.2C)
#   simplify.w  SAT12 전처리와 SAT12-ERP 되살림
#
# examples 아래의 예제들도 모두 문학적 프로그램이다.
#
#   waerden.w  반 데르 바르덴 수
#   queens.w   n-퀸, 해 하나 찾기와 모두 세기
#   sudoku.w   스도쿠 풀기와 해가 하나뿐임의 증명
#   life.w     생명 게임을 거꾸로 돌려 조상 찾기
#   factor.w   곱셈기 회로를 거꾸로 돌려 인수분해하기
#   hamsat.w   컷셋 절을 보태 가며 해밀턴 순환 찾기
#
# knuth/ 아래는 크누스의 원본 CWEB 프로그램이다. 옮길 때 곁에 두고 읽는다.
# testdata/ 아래는 크누스의 SATexamples.tgz에서 고른 작은 문제들이다.
#
# 한글 .w는 kotexgweb을 쓰므로 luatex으로만 조판된다.
#
# GTANGLE/GWEAVE라는 이름을 쓰는 것은 GNU Make에 붙박이로 있는 TANGLE/WEAVE
# 변수(CWEB 연장을 가리킨다)와 부딪히지 않기 위해서다.

GO      ?= go
GTANGLE ?= gtangle
GWEAVE  ?= gweave
LUATEX  ?= luatex -interaction=nonstopmode

LIB      := sat io cdcl simplify
EXAMPLES := waerden queens sudoku life factor hamsat
EXGO     := $(foreach e,$(EXAMPLES),examples/$(e)/$(e).go)
EXPDF    := $(foreach e,$(EXAMPLES),examples/$(e)/$(e).pdf)
JUNK     := tex pdf idx scn log toc dvi

.PHONY: all build test vet tangle pdf check clean

all: build

# .w가 바뀌면 Go 원본을 다시 짜낸다. 글마다 시험 파일도 함께 나온다.
sat.go sat_test.go: sat.w
	$(GTANGLE) $<
	gofmt -w sat.go sat_test.go

io.go io_test.go: io.w
	$(GTANGLE) $<
	gofmt -w io.go io_test.go

cdcl.go cdcl_test.go: cdcl.w
	$(GTANGLE) $<
	gofmt -w cdcl.go cdcl_test.go

simplify.go simplify_test.go: simplify.w
	$(GTANGLE) $<
	gofmt -w simplify.go simplify_test.go

# 예제는 제 디렉터리에서 짜낸다. 정적 패턴 규칙이라 아래의 %-규칙보다 앞선다.
$(EXGO): examples/%.go: examples/%.w
	cd $(dir $@) && $(GTANGLE) $(notdir $<)
	gofmt -w $@

tangle: $(addsuffix .go,$(LIB)) $(EXGO)

build: tangle
	$(GO) build ./...

test: tangle $(addsuffix _test.go,$(LIB))
	$(GO) test ./...

vet: tangle
	$(GO) vet ./...

# 조판은 두 번 돌린다. 상호 참조가 두 번째 판에서 맞춰진다.
pdf: $(addsuffix .pdf,$(LIB)) $(EXPDF)

%.pdf: %.w
	$(GWEAVE) $<
	$(LUATEX) $*.tex
	$(LUATEX) $*.tex

$(EXPDF): examples/%.pdf: examples/%.w
	cd $(dir $@) && $(GWEAVE) $(notdir $<)
	cd $(dir $@) && $(LUATEX) $(notdir $*).tex
	cd $(dir $@) && $(LUATEX) $(notdir $*).tex

# 조판 품질 검사: 로그에 경고나 잘못이 하나라도 있으면 실패한다.
check: pdf
	@bad=0; for f in $(LIB) $(foreach e,$(EXAMPLES),examples/$(e)/$(e)); do \
	  n=$$(grep -ac 'Overfull\|Underfull\|Error\|Missing\|Undefined\|^!' $$f.log); \
	  echo "$$f.log: $$n"; [ "$$n" = 0 ] || bad=1; \
	done; exit $$bad

# clean은 .w가 만들어 낸 것을 지운다. 라이브러리 API의 .go만은 남긴다.
clean:
	rm -f $(addsuffix _test.go,$(LIB))
	rm -f $(foreach x,$(JUNK),$(addsuffix .$(x),$(LIB)))
	rm -f $(EXGO)
	rm -f $(foreach e,$(EXAMPLES),$(foreach x,$(JUNK),examples/$(e)/$(e).$(x)))
	rm -f $(foreach e,$(EXAMPLES),examples/$(e)/$(e))
