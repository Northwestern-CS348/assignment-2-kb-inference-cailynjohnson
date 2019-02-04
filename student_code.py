import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []
    
    def kb_remove(self, fact_or_rule):
        """Helper function of kb_retract that removes a fact or rule from the KB

        Args:
            fact_or_rule - fact or rule to be removed

        Returns:
            None
        """
        printv("Removing {!r}", 0, verbose, [fact_or_rule])


        # if fact_or_rule is a FACT and is in the knowledge base
        if (isinstance(fact_or_rule, Fact)) and fact_or_rule in self.facts:

            # if fact is asserted -> change asserted to false
            if fact_or_rule.asserted == True:
                fact_or_rule.asserted = False 
            
            # if fact is supported (and no longer asserted) -> keep it
            
            # if fact is not supported (and no longer asserted) -> remove it 
            if len(fact_or_rule.supported_by) == 0:

                # if fact supports other facts, adjust the supported_by lists of the supported facts and remove supported facts accordingly
                if len(fact_or_rule.supports_facts) > 0:
                    for currFact in fact_or_rule.supports_facts:
                        currFact = self._get_fact(currFact)
                        for currPair in currFact.supported_by:
                            if currPair[0] == fact_or_rule: # if fact in pair is the fact we're removing
                                currFact.supported_by.remove(currPair) # remove pair from the supported fact's supported_by list
                        if (len(currFact.supported_by) == 0) and currFact.asserted == False: # if supported fact is no longer supported and it's not asserted
                            self.kb_remove(currFact) # remove supported fact from knowledge base

                # if fact supports other rules, adjust the supported_by lists of the supported rules and remove supported rules accordingly 
                if len(fact_or_rule.supports_rules) > 0:
                    for currRule in fact_or_rule.supports_rules:
                        currRule = self._get_rule(currRule)
                        for currPair in currRule.supported_by:
                            if currPair[0] == fact_or_rule: # if fact in pair is the fact we're removing
                                currRule.supported_by.remove(currPair) # remove pair from the supported rule's supported_by list
                        if (len(currRule.supported_by) == 0) and currRule.asserted == False: # if supported rule is no longer supported and it's not asserted
                            self.kb_remove(currRule) # remove supported rule from knowledge base

                # remove fact from knowledge base
                self.facts.remove(fact_or_rule)


        # if fact_or_rule is a RULE and is in the knowledge base
        if (isinstance(fact_or_rule, Rule)) and fact_or_rule in self.rules:

            # if rule is just asserted or both asserted and supported -> keep it

            # if rule is just supported -> keep it

            # if rule is neither asserted nor supported -> remove it
            if (fact_or_rule.asserted == False) and len(fact_or_rule.supported_by) == 0:

                # if rule supports other facts, adjust the supported_by lists of the supported facts and remove supported facts accordingly
                if len(fact_or_rule.supports_facts) > 0:
                    for currFact in fact_or_rule.supports_facts:
                        currFact = self._get_fact(currFact)
                        for currPair in currFact.supported_by:
                            if currPair[1] == fact_or_rule: # if rule in pair is the rule we're removing
                                currFact.supported_by.remove(currPair) # remove pair from the supported fact's supported_by list
                        if (len(currFact.supported_by) == 0) and currFact.asserted == False: # if supported fact is no longer supported and it's not asserted
                            self.kb_remove(currFact)  # remove supported fact from knowledge base

                # if rule supports other rules, adjust the supported_by lists of the supported rules and remove supported rules accordingly
                if len(fact_or_rule.supports_rules) > 0:
                    for currRule in fact_or_rule.supports_rules:
                        currRule = self._get_rule(currRule)
                        for currPair in currRule.supported_by:
                            if currPair[1] == fact_or_rule: # if rule in pair is the rule we're removing
                                currRule.supported_by.remove(currPair) # remove pair from the supported rule's supported_by list
                        if (len(currRule.supported_by) == 0) and currRule.asserted == False: # if supported rule is no longer supported and it's not asserted
                            self.kb_remove(currRule) # remove supported rule from knowledge base
                
                # remove rule from knowledge base
                self.rules.remove(fact_or_rule)



    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        if isinstance (fact_or_rule, Fact): #if fact
            if fact_or_rule in self.facts: #if fact is in knowledge base
                fact = self._get_fact(fact_or_rule) #get fact from knowledge base
                self.kb_remove(fact) #remove fact from knowledge base


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])

        matchBindings = match(rule.lhs[0], fact.statement)

        # if there is a match, infer a new fact or rule
        if matchBindings:

            # if length of left hand side is 1, infer a new fact
            if len(rule.lhs) == 1:
                newStatement = instantiate(rule.rhs, matchBindings)
                newFact = Fact(newStatement, [[fact, rule]]) #makes a new fact while also adding a pair consisting of a fact and a rule to newFact's supported_by list
                fact.supports_facts.append(newFact) #adds new fact to supports_facts list of original fact
                rule.supports_facts.append(newFact) #adds new fact to supports_facts list of original rule
                kb.kb_add(newFact) #adds new fact to knowledge base

            #if length of left hand side is more than 1, infer a new rule
            elif len(rule.lhs) > 1:
                newLHS = [] #creates empty list for left hand side of new rule
                for element in rule.lhs[1:]:
                    newStatement = instantiate(element, matchBindings)
                    newLHS.append(newStatement)
                newRHS = instantiate(rule.rhs, matchBindings)
                newRule = Rule([newLHS, newRHS], [[fact, rule]]) #makes a new rule while also adding a pair consisting of a fact and a rule to newRule's supported_by list
                fact.supports_rules.append(newRule) #adds new rule to supports_rules list of original fact
                rule.supports_rules.append(newRule) #adds new rule supports_rules list of original rule
                kb.kb_add(newRule) #adds new rule to knowledge base
