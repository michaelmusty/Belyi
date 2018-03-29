s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T29-[4,3,6]-4221-333-3222-g0";
s`BelyiDBFilename := "9T29-[4,3,6]-4221-333-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 5, 4, 1, 2, 9, 6, 8, 7, 3 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 9, 1, 6, 8, 7, 3, 5, 4, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 4, 1, 2, 9, 6, 8, 7, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 9, 1, 6, 8, 7, 3, 5, 4, 2 ]:
 Order := 648 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 4, 1, 2, 9, 6, 8, 7, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 9, 1, 6, 8, 7, 3, 5, 4, 2 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 5, 4, 1, 2, 9, 6, 8, 7, 3 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 9, 1, 6, 8, 7, 3, 5, 4, 2 ]:
 Order := 648 > |
[ 5, 4, 1, 2, 9, 6, 8, 7, 3 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 9, 1, 6, 8, 7, 3, 5, 4, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 648 > |
[ 5, 4, 1, 2, 9, 6, 8, 7, 3 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 9, 1, 6, 8, 7, 3, 5, 4, 2 ]
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
