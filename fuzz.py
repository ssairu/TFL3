from collections import defaultdict, deque
import sys
import random
import string

sys.setrecursionlimit(10000)


def isNT(symbol: str) -> bool:
    return not symbol[0].islower()


def getSetOFNTs(rule: list) -> set:
    return set([symbol for symbol in rule if isNT(symbol)])


class Grammar():

    def __init__(self):
        self.NT_To_Rules = defaultdict(list)
        self.rules = []
        self.allNTs = set([])
        self.terminals = set([])
        self.startingNT = None
        self.counter = 1

        self.first = defaultdict(set)
        self.last = defaultdict(set)
        self.follow = defaultdict(set)
        self.precede = defaultdict(set)
        self.followNT = defaultdict(set)
        self.bigramms = defaultdict(set)

        self.NT_To_T_Rules = defaultdict(list)
        self.NT_To_NT_Rules = defaultdict(list)

    def readGrammar(self, startingNT=None):
        lines = sys.stdin.readlines()

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
            for NT2 in getSetOFNTs(rightRule):
                if NT2 not in visited:
                    self.findStartingNTRecursion(NT2, visited)

    def prepareForGeneration(self):
        self.HNFTransform()
        self.makeBigramms()
        self.prepareForCYK()

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

    def HNFTransform(self):
        self.deleteLongRules()
        self.deleteChainRules()
        self.deleteNonGenerative()
        self.deleteNonReacheble()
        self.deleteAloneTerminals()

    def deleteLongRules(self):
        for NT in self.allNTs:
            self.deleteLongRulesRecursion(NT)
        self.updateGrammar()

    def deleteLongRulesRecursion(self, NT: str):
        for i, rightRule in enumerate(self.NT_To_Rules[NT]):
            if len(rightRule) > 2:
                newNT = f"[new_NT_{NT + str(self.counter)}]"
                self.counter += 1
                self.NT_To_Rules[newNT] = [rightRule[1:]]
                newRightRule = [rightRule[0], newNT]
                self.NT_To_Rules[NT][i] = newRightRule
                self.deleteLongRulesRecursion(newNT)

    def deleteChainRules(self):
        visited = set([])
        self.deleteChainRulesRecursion(self.startingNT, visited)
        self.updateGrammar()

    def deleteChainRulesRecursion(self, NT_root: str, visited: set):
        visited.add(NT_root)
        for rightRule in self.NT_To_Rules[NT_root]:
            for NT in getSetOFNTs(rightRule):
                if NT not in visited:
                    self.deleteChainRulesRecursion(NT, visited)
        newRules = []
        for rightRule in self.NT_To_Rules[NT_root]:
            if len(rightRule) == 1 and isNT(rightRule[0]):
                newRules += self.NT_To_Rules[rightRule[0]]
            else:
                newRules.append(rightRule)
        self.NT_To_Rules[NT_root] = newRules.copy()

    def deleteNonGenerative(self):
        isGenerating = defaultdict(bool)
        counter = defaultdict(int)
        concernedRule = defaultdict(list)
        Q = deque()
        allNTs = set([])
        for i, (NT1, rightRule) in enumerate(self.rules):
            count = getSetOFNTs(rightRule)
            allNTs = allNTs.union(count, set([NT1]))
            for NT2 in count:
                concernedRule[NT2] += [i]
            counter[i] += len(count)
            if len(count) == 0:
                isGenerating[NT1] = True
                Q.append(NT1)
        for NT in allNTs:
            if not isGenerating[NT]:
                isGenerating[NT] = False

        visited = set([NT for NT in Q])
        while Q:
            for i in range(len(Q)):
                element = Q.popleft()
                for rule in concernedRule[element]:
                    counter[rule] -= 1
                    if counter[rule] == 0:
                        isGenerating[self.rules[rule][0]] = True
                        if self.rules[rule][0] in visited:
                            continue
                        Q.append(self.rules[rule][0])
                        visited.add(self.rules[rule][0])
        newRules = set([])
        for NT, val in isGenerating.items():
            if not val:
                newRules = set.union(newRules, set(set(concernedRule[NT])))
        self.rules = [rule for i, rule in enumerate(self.rules) if i not in newRules]
        self.NT_To_Rules = defaultdict(list)
        for NT, rightRule in self.rules:
            self.NT_To_Rules[NT] += [rightRule]
        self.updateGrammar()

    def deleteNonReacheble(self):
        rule2rule = defaultdict(list)
        NT_To_RuleNumber = defaultdict(list)
        RuleNumber_To_NTs = defaultdict(set)
        for i, (NT, rightRule) in enumerate(self.rules):
            NT_To_RuleNumber[NT] += [i]
            RuleNumber_To_NTs[i] = getSetOFNTs(rightRule)
        for RuleNumber, NTs in RuleNumber_To_NTs.items():
            for NT in NTs:
                if NT_To_RuleNumber[NT]:
                    rule2rule[RuleNumber] += NT_To_RuleNumber[NT]

        visited = set([])
        for ruleNumber, (NT, _) in enumerate(self.rules):
            if NT == self.startingNT:
                self.deleteNonReachebleRecursion(ruleNumber, visited, rule2rule)

        self.rules = [rule for i, rule in enumerate(self.rules) if i in visited]
        self.NT_To_Rules = defaultdict(list)
        for NT, rightRule in self.rules:
            self.NT_To_Rules[NT] += [rightRule]
        self.updateGrammar()

    def deleteNonReachebleRecursion(self, ruleNumber: int, visited: set, rule2rule: defaultdict):
        visited.add(ruleNumber)
        for next in rule2rule[ruleNumber]:
            if next not in visited:
                self.deleteNonReachebleRecursion(next, visited, rule2rule)

    def deleteAloneTerminals(self):
        newRules = {}
        for i, (NT, rightRule) in enumerate(self.rules):
            count = getSetOFNTs(rightRule)
            if len(rightRule) == 2 and len(count) < 2:
                if not isNT(rightRule[0]):
                    if rightRule[0] not in newRules:
                        newRules[rightRule[0]] = f'[NT_{NT}_To_{rightRule[0]}]'
                    self.rules[i][1][0] = newRules[rightRule[0]]
                if not isNT(rightRule[1]):
                    if rightRule[1] not in newRules:
                        newRules[rightRule[1]] = f'[NT_{NT}_To_{rightRule[1]}]'
                    self.rules[i][1][1] = newRules[rightRule[1]]
        for key, val in newRules.items():
            self.rules.append((val, [key]))

        self.NT_To_Rules = defaultdict(list)
        for NT, rightRule in self.rules:
            self.NT_To_Rules[NT] += [rightRule]
        self.updateGrammar()

    def printGrammar(self):
        for NT, rightRule in self.rules:
            print(NT, '- >', "".join(rightRule))

    def makeBigramms(self):
        self.makeFirstAndLast()
        self.makeFollow()
        self.makePrecede()
        self.useConditions()

    def makeFirstAndLast(self):
        visited = set([])
        for NT in self.allNTs:
            if NT not in visited:
                self.makeFirstAndLastRecursion(NT, visited)

    def makeFirstAndLastRecursion(self, NT, visited):
        visited.add(NT)
        for rightRule in self.NT_To_Rules[NT]:
            if isNT(rightRule[0]):
                if rightRule[0] not in visited:
                    self.makeFirstAndLastRecursion(rightRule[0], visited)
                self.first[NT] = self.first[NT].union(self.first[rightRule[0]])
            else:
                self.first[NT].add(rightRule[0])
            if isNT(rightRule[-1]):
                if rightRule[-1] not in visited:
                    self.makeFirstAndLastRecursion(rightRule[-1], visited)
                self.last[NT] = self.last[NT].union(self.last[rightRule[-1]])
            else:
                self.last[NT].add(rightRule[-1])

    def makeFollow(self):
        changed = True
        while changed:
            changed = False
            for NT, rightRule in self.rules:
                if len(rightRule) > 1:
                    if not all(map(lambda terminal: terminal in self.follow[rightRule[0]], self.first[rightRule[1]])):
                        changed = True
                    self.follow[rightRule[0]] = self.follow[rightRule[0]].union(self.first[rightRule[1]])

    def makePrecede(self):
        changed = True
        while changed:
            changed = False
            for NT, rightRule in self.rules:
                if len(rightRule) > 1:
                    if not all(map(lambda terminal: terminal in self.precede[rightRule[1]], self.last[rightRule[0]])):
                        changed = True
                    self.precede[rightRule[1]] = self.precede[rightRule[1]].union(self.last[rightRule[0]])

    def makeFollowNT(self):
        for _, rightRule in self.rules:
            if len(rightRule) == 2:
                self.followNT[rightRule[0]].add(rightRule[1])

    def useConditions(self):
        for NT, gammas in self.last.items():
            for y1 in gammas:
                for y2 in self.follow[NT]:
                    self.bigramms[y1].add(y2)

        for NT, gammas in self.precede.items():
            for y1 in gammas:
                for y2 in self.first[NT]:
                    self.bigramms[y1].add(y2)

        for NT, val in self.followNT.items():
            for A2 in val:
                for y1 in self.last[NT]:
                    for y2 in self.first[A2]:
                        self.bigramms[y1].add(y2)

    def prepareForCYK(self):
        for NT, rightRule in self.rules:
            if len(rightRule) == 1:
                self.NT_To_T_Rules[NT].append(rightRule[0])
            else:
                self.NT_To_NT_Rules[NT].append(rightRule)

    def CYK(self, word):
        d = {NT: [[False for _ in range(len(word))] for _ in range(len(word))] for NT in self.allNTs}
        for i in range(len(word)):
            for NT, rightRules in self.NT_To_T_Rules.items():
                for rightRule in rightRules:
                    if word[i] == rightRule:
                        d[NT][i][i] = True
        for m in range(1, len(word)):
            for i in range(len(word) - m):
                j = i + m
                for NT, rightRules in self.NT_To_NT_Rules.items():
                    answer = False
                    for rightRule in rightRules:
                        for k in range(i, j):
                            answer = answer or (d[rightRule[0]][i][k] and d[rightRule[1]][k + 1][j])
                    d[NT][i][j] = answer
        return d[self.startingNT][0][len(word) - 1]

    def generate(self,
                 n=100,
                 testing=True,
                 allTerminals=True,
                 randomTerminalChance=0.1,
                 randomStopChance=0.15):
        assert randomTerminalChance + randomStopChance <= 1, "Chances must sum up to 1!"

        terminals = list(self.terminals.copy())
        if allTerminals:
            terminals = string.ascii_lowercase

        startingTerminals = list(self.first[self.startingNT])

        if testing:
            verifyFile = open("verify_file.txt", 'w')
            positiveGenerations = []

        with open("tests.txt", 'w') as f:
            for i in range(n):
                current = random.choice(startingTerminals)
                while self.bigramms[current[-1]]:
                    r = random.random()
                    if r < randomTerminalChance:
                        current += random.choice(terminals)
                    elif r < randomTerminalChance + randomStopChance:
                        break
                    else:
                        current += random.choice(list(self.bigramms[current[-1]]))
                belongsToLanguage = self.CYK(current)
                f.write(f'{current} {1 if belongsToLanguage else 0}\n')
                if testing:
                    verifyFile.write(f'{current}\n')
                    if belongsToLanguage:
                        positiveGenerations.append(str(i + 1))

        if testing:
            print(' '.join(positiveGenerations))
