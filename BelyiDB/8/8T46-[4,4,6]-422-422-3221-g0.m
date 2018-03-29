s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T46-[4,4,6]-422-422-3221-g0";
s`BelyiDBFilename := "8T46-[4,4,6]-422-422-3221-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 5, 4, 6, 2, 8, 3, 1, 7 ],
[ 3, 8, 1, 5, 6, 4, 7, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 5, 4, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 1, 5, 6, 4, 7, 2 ]:
 Order := 576 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 5, 4, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 1, 5, 6, 4, 7, 2 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 5, 4, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 1, 5, 6, 4, 7, 2 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 5, 7, 4, 3, 8, 1, 2, 6 ],
[ 8, 2, 1, 5, 4, 7, 6, 3 ]
],
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 5, 4, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 1, 5, 6, 4, 7, 2 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 4, 6, 5, 1, 2, 3, 8, 7 ],
[ 2, 8, 3, 7, 6, 5, 4, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 5, 4, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 1, 5, 6, 4, 7, 2 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 6, 5, 4, 1, 2, 3, 8, 7 ],
[ 1, 8, 2, 7, 6, 5, 4, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 5, 4, 6, 2, 8, 3, 1, 7 ],
[ 3, 8, 1, 5, 6, 4, 7, 2 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 5, 7, 4, 3, 8, 1, 2, 6 ],
[ 8, 2, 1, 5, 4, 7, 6, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 5, 4, 6, 8, 1, 3, 2, 7 ],
[ 3, 8, 1, 4, 6, 7, 5, 2 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
