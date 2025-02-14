import fuzz
from collections import defaultdict, deque
import sys
from fuzz import Grammar

sys.setrecursionlimit(10000)


def isNT(symbol: str) -> bool:
    return not symbol[0].islower()


def getSetOFNTs(rule: list) -> set:
    return set([symbol for symbol in rule if isNT(symbol)])


class GeneratorPDA:
    def __init__(self, k_param=1):
        self.grammar_str = ''
        self.NT_To_Rules = defaultdict(list)
        self.rules = []
        self.allNTs = set([])
        self.terminals = set([])
        self.startingNT = None
        self.counter = 1
        self.k = k_param

        self.first = defaultdict(set)
        self.follow = defaultdict(set)
        self.parseTable = defaultdict(list)

        self.PDAstates = []
        self.PDAstart = []
        self.PDAfinal = []
        self.PDAstack = deque()
        self.PDAtrans = []
        self.parsing_str = ''
        self.pos = 0
        self.nextk = ''
        self.allready_read = ''

    def readGrammar(self, startingNT=None):
        with open('grammar.txt', 'r') as file:
            self.grammar_str = file.read()
            lines = self.grammar_str.split('\n')

        for line in lines:
            line_splited = list(map(lambda r: r.replace(' ', ''), line.strip().split('->')))
            NT = line_splited[0]
            rightRule = list(map(lambda l: l.strip(), line_splited[1].split('|')))
            self.NT_To_Rules[NT] += list(map(self.parseRule, rightRule))

        self.updateGrammar()

        self.startingNT = startingNT
        if not self.startingNT:
            self.startingNT = self.findStartingNT()

    def findStartingNT(self):
        maxVisited = ("", 0)
        for NT in self.allNTs:
            visited = set([])
            self.findStartingNTRecursion(NT, visited)
            if len(visited) > maxVisited[1]:
                maxVisited = (NT, len(visited))
        return maxVisited[0]

    def findStartingNTRecursion(self, NT1, visited):
        visited.add(NT1)
        for rightRule in self.NT_To_Rules[NT1]:
            for NT2 in fuzz.getSetOFNTs(rightRule):
                if NT2 not in visited:
                    self.findStartingNTRecursion(NT2, visited)

    def updateGrammar(self):
        self.rules = []
        for NT, rightRules in self.NT_To_Rules.items():
            for rightRule in rightRules:
                self.rules.append((NT, rightRule))
        self.allNTs = set(self.NT_To_Rules.keys())

        self.terminals = set([])
        for _, rightRule in self.rules:
            self.terminals = self.terminals.union(set([symbol for symbol in rightRule if not isNT(symbol)]))

    def parseRule(self, s: str) -> list:
        newList = []
        i = 0
        while i < len(s):
            if s[i] == '[':
                start = i
                while s[i] != ']':
                    i += 1
                newList.append(s[start:i + 1])
            else:
                if i < len(s) - 1 and s[i + 1].isnumeric():
                    newList.append(s[i:i + 2])
                    i += 1
                else:
                    newList.append(s[i])
            i += 1

        return newList

    def getFirstK(self, str):
        return str[:self.k]

    def FirstK_concatStringSets(self, sets):
        if len(sets) == 1:
            return sets[0]

        if sets[0] == set([]):
            return set([])
        else:
            result = sets[0]

        if sets[1] == set([]):
            return set([])

        new_result = set([])
        for x in result:
            new_result = new_result.union(set(map(lambda r: self.getFirstK(x + r), sets[1])))
        result = new_result

        return self.FirstK_concatStringSets([result] + sets[2:])

    def createFirst(self):
        new_first = defaultdict(set)
        for NT in self.allNTs:
            new_first[NT] = set([])

        for T in self.terminals:
            new_first[T] = {T}

        while not (self.first == new_first):
            for key, value in new_first.items():
                self.first[key] = value

            for NT, rule in self.rules:
                new_first[NT] = new_first[NT].union(
                    self.FirstK_concatStringSets([new_first[symbol] for symbol in rule]))

    def createFollow(self):
        new_follow = defaultdict(set)
        new_follow[self.startingNT] = {""}  # "" == epsilon

        for NT in self.allNTs:
            if not NT == self.startingNT:
                new_follow[NT] = set([])

        while not (self.follow == new_follow):
            for key, value in new_follow.items():
                self.follow[key] = value

            for NT, rule in self.rules:
                for i, symbol in enumerate(rule):
                    if isNT(symbol):
                        new_follow[symbol] = new_follow[symbol].union(
                            self.FirstK_concatStringSets([self.first[s] for s in rule[i + 1:]] +
                                                         [new_follow[NT]]))

    def createParseTable(self, startingNT=None):
        self.readGrammar(startingNT)
        self.createFirst()
        self.createFollow()

        parseTable = defaultdict(set)
        for NT, rule in self.rules:
            for x in self.FirstK_concatStringSets([self.first[s] for s in rule] + [self.follow[NT]]):
                parseTable[(NT, x)] = parseTable[(NT, x)].union({tuple(rule)})

        for key, value in parseTable.items():
            self.parseTable[key] = list(value)

        with open('ParseTable.txt', 'w', encoding='utf-8') as f:
            data = ''
            for key, rules in parseTable.items():
                for rule in rules:
                    rule_str = ''
                    for term in rule:
                        rule_str = rule_str + term + '.'
                    rule_str = rule_str[:-1]
                    data = data + key[0] + ':' + key[1] + '>' + rule_str + '\n'
            f.write(data)

    def readParseTable(self):
        parseTable = defaultdict(set)

        with open('ParseTable.txt', 'r') as f:
            data = f.readlines()
            data_form = [s.strip('\n').split('>') for s in data]
        for table_elem in data_form:
            key = tuple(table_elem[0].split(':'))
            rule = tuple(table_elem[1].split('.'))
            parseTable[key] = parseTable[key].union({rule})

        for key, value in parseTable.items():
            self.parseTable[key] = list(value)

    # def read_term(self, symbol):
    #     self.allready_read += symbol
    #     if self.parsing_str[self.pos] == symbol:
    #         self.pos += 1
    #         self.nextk = self.getFirstK(self.parsing_str[self.pos:])
    #         return True
    #     else:
    #         return False
    #
    # def SymbolRecursion(self, symbol):
    #     if symbol in self.terminals:
    #         same_term = self.read_term(symbol)
    #         if not same_term:
    #             return False
    #     elif symbol in self.allNTs:
    #         rules = self.parseTable[(symbol, self.nextk)]
    #         if not rules:
    #             return False
    #         for rule in rules:
    #             all_parts_good = True
    #             for r_symb in rule:
    #                 res = self.SymbolRecursion(r_symb)
    #                 if not res:
    #                     all_parts_good = False
    #             if all_parts_good:
    #                 return True
    #     else:
    #         return False

    def checkWord(self, word, tree=True):
        # Старый красивый код для рекурсии, удалять жалко а недетерминизм на нём реализовать
        # не придумал как, поэтому переписал всё на стек.


        # self.pos = 0
        # self.parsing_str = word
        # self.nextk = self.getFirstK(self.parsing_str)
        # self.SymbolRecursion(self.startingNT)
        # print(self.allready_read)
        #
        # if self.pos == len(word):
        #     return True
        # else:
        #     print('wrong pos: ' + str(self.pos) + '   len: ' + str(len(word)))
        #     return False

        stacks = [([self.startingNT], 0, self.getFirstK(word))]
        success = False

        while stacks:
            if tree:
                print(stacks)
            delete_indexes = []
            for i in range(len(stacks)):
                if not stacks[i][0]:
                    delete_indexes.append(i)
                    if stacks[i][1] == len(word):
                        success = True
                        break
                    else:
                        continue
                symbol = stacks[i][0].pop()
                pos = stacks[i][1]
                nextk = stacks[i][2]
                if symbol in self.terminals:
                    if pos < len(word) and word[pos] == symbol:
                        stacks[i] = (stacks[i][0], pos + 1, self.getFirstK(word[pos + 1:]))
                    else:
                        delete_indexes.append(i)
                        continue
                elif symbol in self.allNTs:
                    rules = self.parseTable[(symbol, nextk)]

                    new_rules = []
                    leni = len(stacks[i][0])
                    for rule in rules:
                        if leni + len(rule) <= len(word[pos:]):
                            new_rules.append(rule)
                    rules = new_rules

                    if not rules:
                        delete_indexes.append(i)
                        continue
                    else:
                        stack_i = stacks[i]
                        stacks[i] = (stack_i[0] + list(reversed(rules[0])), pos, nextk)
                        for rule in rules[1:]:
                            stacks.append((stack_i[0] + list(reversed(rule)), stack_i[1], stack_i[2]))
                else:
                    print('НЕДОСТИЖИМО И СТРАННО')
                    print(stacks[i][0])

            new_stacks = []
            for i in range(len(stacks)):
                if not (i in delete_indexes):
                    new_stacks.append(stacks[i])
            stacks = new_stacks

        return success

    def check_ll_k(self, startingNT=None):
        self.createParseTable(startingNT='S')
        ll_mark = True
        for rules in self.parseTable.values():
            if len(rules) > 1:
                ll_mark = False
        return ll_mark

    def get_examples(self, n=None, testing=False, allTerminals=True):
        grammar = Grammar()
        grammar.readGrammar(startingNT=self.startingNT)
        grammar.prepareForGeneration()
        grammar.generate(n=n, testing=testing, allTerminals=allTerminals)

    def test_examples(self, tree=False):
        with open('tests.txt', 'r') as file:
            lines = file.readlines()

        lines = [tuple(line.strip().split()) for line in lines]
        print(lines)
        every_good = True
        for word, mark in lines:
            res = self.checkWord(word, tree)
            if res and mark == '0':
                print('wrong - ' + word + ' ' + mark + '    res: ' + str(self.checkWord(word)))
                every_good = False
            elif not res and mark == '1':
                print('wrong - ' + word + ' ' + mark + '    res: ' + str(self.checkWord(word)))
                every_good = False

        return every_good








def main():
    k = int(input('введите k: '))
    if k < 1:
        print('k должно быть целым числом и больше 0')
        return


    PDA = GeneratorPDA(k)
    PDA.createParseTable(startingNT='S')
    print(PDA.checkWord('bb'))
    # PDA.get_examples(1000)
    # print(PDA.test_examples())
    # PDA.readParseTable()


    # print(PDA.first)
    # print(PDA.follow)
    # print(PDA.parseTable)


if __name__ == "__main__":
    main()
